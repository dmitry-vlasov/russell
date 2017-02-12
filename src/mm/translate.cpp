#include <boost/algorithm/string.hpp>

#include "mm/sys.hpp"
#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "mm/tree.hpp"

namespace mdl { namespace mm { namespace {

void gather_expr_vars(set<Symbol>& vars, const Vect& expr) {
	for (Symbol s : expr)
		if (s.var) vars.insert(s);
}

void gather_inner_vars(const set<Symbol>& fvars,
	set<Symbol>& ivars, set<Symbol>& avars, const Proof* proof) {
	if (!proof) return;
	for (Ref* n : proof->refs) {
		if (n->type == Ref::FLOATING) {
			Symbol v = n->val.flo->var();
			avars.insert(v);
			if (fvars.find(v) == fvars.end())
				ivars.insert(v);
		}
	}
}

struct Scope {
	deque<Variables*>  vars;
	deque<Disjointed*> disj;
	deque<Floating*>   flos;
	deque<Essential*>  esss;
	deque<Node>        args;
};

vector<Scope> scope_stack;

struct Maps {
	map<const mm::Theorem*,   smm::Assertion*> theorems;
	map<const mm::Axiom*,     smm::Assertion*> axioms;
	map<const mm::Essential*, smm::Essential*> essentials;
	map<const mm::Floating*,  smm::Floating*>  floatings;
	map<const mm::Floating*,  smm::Inner*>     inners;
	map<const mm::Source*,    smm::Source*>    sources;
	Transform transform;
};

struct Context {
	Maps maps;
	vector<Scope> scope_stack;
};

Scope gather_scope(const vector<Scope>& scope_stack) {
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
void reduce_floatings(smm::Assertion* ass, const set<Symbol>& flo_vars, const set<Symbol>& inn_vars, Context& ctx) {
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
				ctx.maps.floatings.begin(),
				ctx.maps.floatings.end(),
				[flo](std::pair<const Floating*, smm::Floating*> p) { return p.second == flo; }
				)->first;
			ctx.maps.floatings.erase(mm_flo);
			ctx.maps.inners[mm_flo] = red_inns.back();
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

smm::Proof* translate_proof(Context& ctx, const Proof* mproof) {
	smm::Proof* sproof = new smm::Proof();
	for (auto ref : mproof->refs) {
		Ref::Value val = ref->val;
		switch (ref->type) {
		case Ref::FLOATING:
			if (ctx.maps.floatings.count(val.flo))
				sproof->refs.push_back(new smm::Ref(ctx.maps.floatings[val.flo]));
			else
				sproof->refs.push_back(new smm::Ref(ctx.maps.inners[val.flo]));
			break;
		case Ref::ESSENTIAL:
			sproof->refs.push_back(new smm::Ref(ctx.maps.essentials[val.ess])); break;
		case Ref::AXIOM:
			sproof->refs.push_back(new smm::Ref(val.ax->label, true)); break;
		case Ref::THEOREM:
			sproof->refs.push_back(new smm::Ref(val.th->label, false)); break;
		default : assert(false && "impossible"); break;
		}
	}
	return sproof;
}

void reduce(Context& ctx, smm::Assertion* ass, ArgMap& args, const Proof* proof) {
	// Gather the variables, used in assertion hypotheses and statement (header).
	set<Symbol> flo_vars;
	for (auto ess : ass->essential) {
		gather_expr_vars(flo_vars, ess->expr);
	}
	gather_expr_vars(flo_vars, ass->prop->expr);

	// Gather the variables, used in proof but not in header, and collect all vars.
	set<Symbol> inn_vars;
	set<Symbol> all_vars(flo_vars);
	gather_inner_vars(flo_vars, inn_vars, all_vars, proof);

	reduce_variables(ass, all_vars);
	reduce_disjointed(ass, all_vars);
	reduce_permutation(ass, flo_vars, args);
	reduce_floatings(ass, flo_vars, inn_vars, ctx);
	reindex_essentials(ass);

	ctx.maps.transform[ass->prop->label] = args.create_permutation();
}

smm::Proof* transform_proof(Context& ctx, set<uint>& red, const Proof* proof) {
	Proof* tree = to_tree(proof);
	if (tree == nullptr)
		return nullptr;
	reduce(tree, red);
	transform(tree, ctx.maps.transform);
	Proof* rpn = to_rpn(tree);
	smm::Proof* pr = translate_proof(ctx, rpn);
	delete tree;
	delete rpn;
	return pr;
}

void add(Context& ctx, const Scope& scope, smm::Assertion* ass) {
	for (auto var : scope.vars)
		ass->variables.push_back(new smm::Variables { var->expr });
	for (auto dis : scope.disj)
		ass->disjointed.push_back(new smm::Disjointed { dis->expr });
	for (auto ess : scope.esss) {
		ass->essential.push_back(new smm::Essential {ess->label, ess->expr });
		ctx.maps.essentials[ess] = ass->essential.back();
	}
	for (auto flo : scope.flos) {
		ass->floating.push_back(new smm::Floating {flo->label, flo->expr });
		ctx.maps.floatings[flo] = ass->floating.back();
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
			a_map.args.push_back(ArgMap::Arg { n.val.ess->label, ess_ind ++});
		else if (n.type == Node::FLOATING)
			a_map.args.push_back(ArgMap::Arg { n.val.flo->label, ess_num + flo_ind ++});
		else
			assert(false && "impossible");
	}
	return a_map;
}

smm::Assertion* translate_ass(Context& ctx, const Node& n, const Block* block)  {
	smm::Assertion* ass = new smm::Assertion();
	static set<uint> red;
	ass->prop = new smm::Proposition(n.type == Node::AXIOM, n.label(), n.expr());

	Scope scope = gather_scope(ctx.scope_stack);
	add(ctx, scope, ass);
	ArgMap args = arg_map(scope.args);

	reduce(ctx, ass, args, n.proof());
	n.arity() = ass->essential.size() + ass->floating.size();
	if (n.type == Node::THEOREM) {
		ass->proof = transform_proof(ctx, red, n.val.th->proof);
		if (!ass->proof) {
			// Dummy (redundant) theorem
			red.insert(n.label());
			delete ass;
			ass = nullptr;
		} else {
			ctx.maps.theorems[n.val.th] = ass;
		}
	} else {
		ctx.maps.axioms[n.val.ax] = ass;
	}
	return ass;
}

void translate_block(Context& ctx, const Block* source, smm::Source* target);
smm::Source* translate_source(Context& ctx, const Source* src);

void translate_node(Context& ctx, const Node& node, const Block* block, smm::Source* target) {
	switch(node.type) {
	case Node::COMMENT: {
		smm::Comment* c = new smm::Comment(node.val.com->text);
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::CONSTANTS: {
		smm::Constants* c = new smm::Constants { node.val.cst->expr };
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::THEOREM:
	case Node::AXIOM: {
		smm::Assertion* ass = translate_ass(ctx, node, block);
		if (ass) target->contents.push_back(smm::Node(ass));
	} break;
	case Node::BLOCK:
		node.val.blk->ind = node.ind;
		scope_stack.push_back(Scope());
		translate_block(ctx, node.val.blk, target);
		scope_stack.pop_back();
		break;
	case Node::INCLUSION: {
		smm::Source* s = translate_source(ctx, node.val.inc->source);
		smm::Inclusion* i = new smm::Inclusion(s->label);
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

void translate_block(Context& ctx, const Block* source, smm::Source* target) {
	for (auto& node : source->contents) {
		translate_node(ctx, node, source, target);
	}
}

Path translate_path(Path path, bool deep = false) {
	return Path(deep ? path.name : Sys::conf().in);
}


smm::Source* translate_source(Context& ctx, const Source* src) {
	if (ctx.maps.sources.count(src)) {
		return ctx.maps.sources[src];
	} else {
		smm::Source* target = new smm::Source(src->label);
		ctx.maps.sources[src] = target;
		translate_block(ctx, src->block, target);
		return target;
	}
}

} // anonymous

smm::Source* translate(const Source* source) {
	Context context;
	scope_stack.push_back(Scope());
	smm::Source* target = translate_source(context, source);
	scope_stack.pop_back();
	return target;
}

}} // mdl::mm

