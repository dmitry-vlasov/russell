//#include <boost/algorithm/string.hpp>

#include "mm/sys.hpp"
#include "smm/ast.hpp"
#include "mm/ast.hpp"

namespace mdl { namespace mm { namespace {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;

struct Tree {
	struct Node {
		enum Type {
			REF,
			TREE
		};
		union Value {
			Value(Ref* r) : ref(r) { }
			Value(Tree* t) : tree(t) { }
			Value(const Value& v) : ref(v.ref) { }
			Ref*  ref;
			Tree* tree;
		};
		Node(Ref* r) : type(REF), val(r) { }
		Node(Tree* t) : type(TREE), val(t) { }
		void destroy() { if (type == TREE) delete val.tree; }
		uint length() const {
			return (type == Tree::Node::TREE) ? val.tree->length() : 1;
		}
		string show() const {
			return (type == Tree::Node::TREE) ? val.tree->show() : Lex::toStr(val.ref->label());
		}
		Type type;
		Value val;
	};
	Tree() = default;
	Tree(Ref* r) { nodes.push_back(r); }
	~Tree() { for (auto& n : nodes) n.destroy(); }
	uint length() const {
		uint len = 0;
		for (auto& n : nodes) len += n.length();
		return len;
	}
	string show() const {
		string space = length() > 16 ? "\n" : " ";
		assert(nodes.back().type == Tree::Node::REF);
		string str = Lex::toStr(nodes.back().val.ref->label());
		str += "(";
		for (uint i = 0; i + 1 < nodes.size(); ++ i)
			str += Indent::paragraph(space + nodes[i].show(), "  ");
		str += space + ") ";
		return str;
	}
	vector<Node> nodes;
};

Tree* to_tree(const Proof* proof) {
	stack<Tree*> stack;
	for (auto r : proof->refs) {
		switch(r->type()) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
			stack.push(new Tree(r));
			break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Tree* t = new Tree();
			t->nodes.push_back(r);
			for (uint i = 0; i < r->arity(); ++ i) {
				t->nodes.push_back(stack.top());
				stack.pop();
			}
			std::reverse(t->nodes.begin(), t->nodes.end());
			stack.push(t);
		}	break;
		default : assert(false && "impossible"); break;
		}
	}
	Tree* tree = stack.top();
	stack.pop();
	if (!stack.empty())
		throw Error("non-empty stack at the end of the proof");
	return tree;
}

static void to_proof(const Tree* t, vector<Ref*>& proof) {
	for (auto n : t->nodes) {
		switch(n.type) {
		case Tree::Node::REF:
			proof.push_back(new Ref(*n.val.ref));
			break;
		case Tree::Node::TREE:
			to_proof(n.val.tree, proof);
			break;
		default : assert(false && "impossible"); break;
		}
	}
}

Proof* to_proof(const Tree* tree) {
	Proof* proof = new Proof();
	to_proof(tree, proof->refs);
	return proof;
}

void transform(Tree* tree, const Transform& trans, bool forward = true) {
	for (uint i = 0; i < tree->nodes.size() - 1; ++ i) {
		if (tree->nodes[i].type == Tree::Node::TREE)
			transform(tree->nodes[i].val.tree, trans, forward);
	}
	assert(tree->nodes.back().type == Tree::Node::REF);
	Ref* op = tree->nodes.back().val.ref;
	if (op->type() == Ref::AXIOM || op->type() == Ref::THEOREM) {
		Perm perm = trans.at(op->label());
		assert(perm.size() + 1 == tree->nodes.size());
		vector<Tree::Node> new_nodes = tree->nodes;
		for (uint i = 0; i < new_nodes.size() - 1; ++ i) {
			if (forward) new_nodes[perm[i]] = tree->nodes[i];
			else         new_nodes[i] = tree->nodes[perm[i]];
		}
		tree->nodes = new_nodes;
	}
}

Tree* reduce(Tree* tree, const map<uint, Ref*>& red) {
	assert(tree->nodes.back().type == Tree::Node::REF);
	uint l = tree->nodes.back().val.ref->label();
	if (red.count(l)) {
		Ref* ref = red.at(l);
		Tree* t = nullptr;
		if (ref->is_assertion()) {
			t = new Tree(ref);
		} else {
			const uint arg = tree->nodes.size() - 2;
			assert(tree->nodes[arg].type == Tree::Node::TREE);
			std::swap(tree->nodes[arg].val.tree, t);
		}
		delete tree;
		return reduce(t, red);
	} else {
		for (auto& n : tree->nodes)
			if (n.type == Tree::Node::TREE)
				n.val.tree = reduce(n.val.tree, red);
		return tree;
	}
}

void gather_expr_vars(set<Symbol>& vars, const Vect& expr) {
	for (Symbol s : expr)
		if (s.var) vars.insert(s);
}

void gather_inner_vars(const set<Symbol>& fvars,
	set<Symbol>& ivars, set<Symbol>& avars, const Proof* proof) {
	if (!proof) return;
	for (Ref* r : proof->refs) {
		if (r->type() == Ref::FLOATING) {
			Symbol v = r->flo()->var();
			avars.insert(v);
			if (fvars.find(v) == fvars.end())
				ivars.insert(v);
		}
	}
}

struct Maps {
	map<const mm::Theorem*,   smm::Assertion*> theorems;
	map<const mm::Axiom*,     smm::Assertion*> axioms;
	map<const mm::Essential*, smm::Essential*> essentials;
	map<const mm::Floating*,  smm::Floating*>  floatings;
	map<const mm::Floating*,  smm::Inner*>     inners;
	map<const mm::Source*,    smm::Source*>    sources;
	map<uint, Ref*> redundant;
	Transform transform;
};

// Replace variable sets with single set, which contains only needed variables.
//
void reduce_variables(smm::Assertion* ass, const set<Symbol>& all_vars) {
	Vect rvars;
	for (const smm::Variables* vars : ass->variables) {
		for (Symbol v : vars->expr) {
			if (all_vars.find(v) != all_vars.end())
				rvars += v;
		}
		delete vars;
	}
	ass->variables.clear();
	if (!rvars.empty())
		ass->variables.push_back(new smm::Variables { rvars });
}

// Replace variable sets with single set, which contains only needed variables.
//
void reduce_disjointed(smm::Assertion* ass, const set<Symbol>& all_vars) {
	vector<smm::Disjointed*> red_disjs;
	for (auto disj : ass->disjointed) {
		smm::Disjointed* red_disj = new smm::Disjointed();
		for (Symbol s : disj->expr) {
			if (all_vars.find(s) != all_vars.end())
				red_disj->expr.push_back(s);
		}
		if (red_disj->expr.size() > 1)
			red_disjs.push_back(red_disj);
		else {
			delete red_disj;
		}
		delete disj;
	}
	ass->disjointed = red_disjs;
}

// Remove floatings, which variable is not needed, and switch those flos,
// which are used only in proof to inner.
//
void reduce_floatings(smm::Assertion* ass, const set<Symbol>& flo_vars,
	const set<Symbol>& inn_vars, Maps& maps) {
	vector<smm::Floating*> red_flos;
	vector<smm::Inner*>    red_inns;
	uint flo_ind = 0;
	uint inn_ind = 0;
	for (auto flo : ass->floating) {
		if (flo_vars.find(flo->var()) != flo_vars.end()) {
			flo->index = flo_ind ++;
			red_flos.push_back(flo);
			continue;
		}
		if (inn_vars.find(flo->var()) != inn_vars.end()) {
			flo->index = inn_ind ++;
			red_inns.push_back(new smm::Inner {flo->index, flo->expr});
			const Floating* mm_flo =
				std::find_if(
				maps.floatings.begin(),
				maps.floatings.end(),
				[flo](std::pair<const Floating*, smm::Floating*> p) { return p.second == flo; }
				)->first;
			maps.floatings.erase(mm_flo);
			maps.inners[mm_flo] = red_inns.back();
		}
		delete flo;
	}
	ass->floating = red_flos;
	ass->inner = red_inns;
}

void reindex_essentials(smm::Assertion* ass) {
	uint ess_ind = 0;
	for (auto ess : ass->essential) {
		ess->index = ess_ind ++;
	}
}


struct ArgMap;

//ostream& operator << (ostream&, const ArgMap&);

struct ArgMap {
	struct Arg {
		uint label;
		uint ind;
	};
	typedef vector<Arg>::iterator Iter;

	Perm create_permutation() {
		Perm perm;
		for (uint i = 0; i < args.size(); ++ i)
			perm[i] = args[i].ind;
		return perm;
	}
	void remove(uint label) {
		Iter found = args.end();
		Iter begin = args.begin();
		Iter end   = args.end();
		uint found_ind = -1;
		for (auto it = begin; it != end; ++ it) {
			if (it->ind > found_ind)
				-- it->ind;
			if (it->label == label) {
				found = it;
				found_ind = it->ind;
			}
		}
		if (found != end) args.erase(found);
		assert(verify());
	}
	bool verify() {
		vector<uint> c(args.size(), 0);
		for (Arg arg : args) {
			++ c[arg.ind];
		}
		return std::count(c.begin(), c.end(), 1) == (int)args.size();
	}
	vector<Arg> args;
};
/*
ostream& operator << (ostream& os, const ArgMap& amap) {
	os << endl;
	for (uint i = 0; i < amap.args.size(); ++ i) {
		ArgMap::Arg arg = amap.args[i];
		os << show(arg.label) << ": " << i << " -> " << arg.ind << endl;
	}
	return os;
}
*/
// Reduce permutation, remove variable which are not needed.
//
void reduce_permutation(smm::Assertion* ass, const set<Symbol>& needed, ArgMap& args) {
	for (auto flo : ass->floating) {
		if (needed.find(flo->var()) == needed.end()) {
			args.remove(flo->index);
		}
	}
}

smm::Proof* translate_proof(Maps& maps, const Proof* mproof) {
	smm::Proof* sproof = new smm::Proof();
	for (auto r : mproof->refs) {
		switch (r->type()) {
		case Ref::FLOATING:
			if (maps.floatings.count(r->flo()))
				sproof->refs.push_back(new smm::Ref(maps.floatings[r->flo()]));
			else
				sproof->refs.push_back(new smm::Ref(maps.inners[r->flo()]));
			break;
		case Ref::ESSENTIAL:
			sproof->refs.push_back(new smm::Ref(maps.essentials[r->ess()])); break;
		case Ref::AXIOM:
			sproof->refs.push_back(new smm::Ref(maps.axioms[r->axm()]->prop.label, true)); break;
		case Ref::THEOREM:
			sproof->refs.push_back(new smm::Ref(maps.theorems[r->thm()]->prop.label, false)); break;
		default : assert(false && "impossible"); break;
		}
	}
	return sproof;
}

void reduce(Maps& maps, smm::Assertion* ass, ArgMap& args, const Proof* proof) {
	// Gather the variables, used in assertion hypotheses and statement (header).
	set<Symbol> flo_vars;
	for (auto ess : ass->essential) {
		gather_expr_vars(flo_vars, ess->expr);
	}
	gather_expr_vars(flo_vars, ass->prop.expr);

	// Gather the variables, used in proof but not in header, and collect all vars.
	set<Symbol> inn_vars;
	set<Symbol> all_vars(flo_vars);
	gather_inner_vars(flo_vars, inn_vars, all_vars, proof);

	reduce_variables(ass, all_vars);
	reduce_disjointed(ass, all_vars);
	reduce_permutation(ass, flo_vars, args);
	reduce_floatings(ass, flo_vars, inn_vars, maps);
	reindex_essentials(ass);

	maps.transform[ass->prop.label] = args.create_permutation();
}

smm::Proof* transform_proof(Maps& maps, const Proof* proof) {
	Tree* tree = to_tree(proof);
	if (tree->nodes.front().type == Tree::Node::REF) {
		delete tree;
		return nullptr;
	}
	tree = reduce(tree, maps.redundant);
	transform(tree, maps.transform);
	Proof* rpn = to_proof(tree);
	smm::Proof* pr = translate_proof(maps, rpn);
	delete tree;
	delete rpn;
	return pr;
}

struct Scope {
	deque<Variables*>  vars;
	deque<Disjointed*> disj;
	deque<Floating*>   flos;
	deque<Essential*>  esss;
	deque<Node>        args;
};

vector<Scope> scope_stack;

Scope gather_scope() {
	Scope scope;
	for (auto& s : scope_stack) {
		for (auto v : s.vars) scope.vars.push_back(v);
		for (auto d : s.disj) scope.disj.push_back(d);
		for (auto f : s.flos) scope.flos.push_back(f);
		for (auto e : s.esss) scope.esss.push_back(e);
		for (auto a : s.args) scope.args.push_back(a);
	}
	return scope;
}

void add(Maps& maps, const Scope& scope, smm::Assertion* ass) {
	for (auto var : scope.vars)
		ass->variables.push_back(new smm::Variables { var->expr });
	for (auto dis : scope.disj)
		ass->disjointed.push_back(new smm::Disjointed { dis->expr });
	for (auto ess : scope.esss) {
		ass->essential.push_back(new smm::Essential {ess->id(), ess->expr });
		maps.essentials[ess] = ass->essential.back();
	}
	for (auto flo : scope.flos) {
		ass->floating.push_back(new smm::Floating {flo->id(), flo->expr });
		maps.floatings[flo] = ass->floating.back();
	}
}

ArgMap arg_map(const deque<Node>& ar_orig) {
	uint ess_num = std::count_if(
		ar_orig.begin(),
		ar_orig.end(),
		[](const Node& n) { return n.type == Node::ESSENTIAL; }
	);
	ArgMap a_map;
	uint ess_ind = 0;
	uint flo_ind = 0;
	for (uint i = 0; i < ar_orig.size(); ++ i) {
		Node n = ar_orig[i];
		if (n.type == Node::ESSENTIAL)
			a_map.args.push_back(ArgMap::Arg { n.val.ess->id(), ess_ind ++});
		else if (n.type == Node::FLOATING)
			a_map.args.push_back(ArgMap::Arg { n.val.flo->id(), ess_num + flo_ind ++});
		else
			assert(false && "impossible");
	}
	return a_map;
}

smm::Assertion* translate_ass(Maps& maps, const Node& n, const Block* block)  {
	smm::Assertion* ass = new smm::Assertion(n.label());
	ass->prop = smm::Proposition {n.type == Node::AXIOM, n.label(), n.expr()};

	Scope scope = gather_scope();
	add(maps, scope, ass);
	ArgMap args = arg_map(scope.args);

	reduce(maps, ass, args, n.proof());
	n.arity() = ass->essential.size() + ass->floating.size();

	if (n.type == Node::THEOREM) {
		ass->proof = transform_proof(maps, n.val.th->proof);
		if (!ass->proof) {
			// Dummy (redundant) theorem
			assert(n.proof()->refs.size() == 1);
			maps.redundant[n.label()] = n.proof()->refs[0];
			delete ass;
			ass = nullptr;
		} else {
			maps.theorems[n.val.th] = ass;
		}
	} else {
		maps.axioms[n.val.ax] = ass;
	}
	return ass;
}

void translate_block(Maps& maps, const Block* source, smm::Source* target);
smm::Source* translate_source(Maps& maps, const Source* src, smm::Source* target = nullptr);

void translate_node(Maps& maps, const Node& node, const Block* block, smm::Source* target) {
	switch(node.type) {
	case Node::COMMENT: {
		smm::Comment* c = new smm::Comment(node.val.com->text);
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::CONSTANT: {
		smm::Constant* c = new smm::Constant { node.val.cst->symb };
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::THEOREM:
	case Node::AXIOM: {
		smm::Assertion* ass = translate_ass(maps, node, block);
		if (ass) target->contents.push_back(smm::Node(ass));
	} break;
	case Node::BLOCK:
		node.val.blk->ind = node.ind;
		scope_stack.push_back(Scope());
		translate_block(maps, node.val.blk, target);
		scope_stack.pop_back();
		break;
	case Node::INCLUSION: {
		smm::Source* s = translate_source(maps, node.val.inc->source);
		smm::Inclusion* i = new smm::Inclusion(s, node.val.inc->primary);
		target->contents.push_back(smm::Node(i));
	} break;
	case Node::VARIABLES:
		scope_stack.back().vars.push_back(node.val.var); break;
	case Node::DISJOINTED:
		scope_stack.back().disj.push_back(node.val.dis); break;
	case Node::FLOATING:
		scope_stack.back().args.push_back(node);
		scope_stack.back().flos.push_back(node.val.flo); break;
	case Node::ESSENTIAL:
		scope_stack.back().args.push_back(node);
		scope_stack.back().esss.push_back(node.val.ess); break;
	default :
		cout << node << endl;
		assert(false && "impossible"); break;
	}
}

void translate_block(Maps& maps, const Block* source, smm::Source* target) {
	for (auto& node : source->contents) {
		translate_node(maps, node, source, target);
	}
}

smm::Source* translate_source(Maps& maps, const Source* src, smm::Source* target) {
	if (maps.sources.count(src)) {
		return maps.sources[src];
	} else {
		if (!target) target = new smm::Source(src->id());
		maps.sources[src] = target;
		translate_block(maps, src->block, target);
		return target;
	}
}

}

void translate(uint src, uint tgt) {
	Sys::timer()["translate"].start();
	Maps maps;
	scope_stack.push_back(Scope());
	const Source* s = Sys::get().math.get<Source>().access(src);
	translate_block(maps, s->block, new smm::Source(tgt));
	scope_stack.pop_back();
	Sys::timer()["translate"].stop();
}

}} // mdl::mm

