#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "mm/tree.hpp"
#include "mm/globals.hpp"

namespace mdl { namespace mm {

static void gather_expr_vars(set<Symbol>& vars, const Expr& expr) {
	for (Symbol s : expr.symbols)
		if (s.var) vars.insert(s);
}

static void gather_inner_vars(const set<Symbol>& fvars,
	set<Symbol>& ivars, set<Symbol>& avars, const Proof* proof) {
	if (!proof) return;
	for (Ref n : proof->refs) {
		if (n.type == Ref::FLOATING) {
			Symbol v = n.val.flo->var();
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
	Transform transform;
};

// Replace variable sets with single set, which contains only needed variables.
//
static void reduce_variables(smm::Assertion* ass, const set<Symbol>& all_vars) {
	Expr rvars;
	for (const smm::Variables* vars : ass->variables) {
		for (Symbol v : vars->expr.symbols) {
			if (all_vars.find(v) != all_vars.end())
				rvars += v;
		}
		delete vars;
	}
	ass->variables.clear();
	if (!rvars.symbols.empty())
		ass->variables.push_back(new smm::Variables { rvars });
}

// Replace variable sets with single set, which contains only needed variables.
//
static void reduce_disjointed(smm::Assertion* ass, const set<Symbol>& all_vars) {
	vector<smm::Disjointed*> red_disjs;
	for (auto disj : ass->disjointed) {
		smm::Disjointed* red_disj = new smm::Disjointed();
		for (Symbol s : disj->expr.symbols) {
			if (all_vars.find(s) != all_vars.end())
				red_disj->expr.push_back(s);
		}
		if (red_disj->expr.symbols.size() > 1)
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
static void reduce_floatings(smm::Assertion* ass, const set<Symbol>& flo_vars,
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

static void reindex_essentials(smm::Assertion* ass) {
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

ostream& operator << (ostream& os, const ArgMap& amap) {
	os << endl;
	for (uint i = 0; i < amap.args.size(); ++ i) {
		ArgMap::Arg arg = amap.args[i];
		os << label(arg.label) << ": " << i << " -> " << arg.ind << endl;
	}
	return os;
}

// Reduce permutation, remove variable which are not needed.
//
static void reduce_permutation(smm::Assertion* ass, const set<Symbol>& needed, ArgMap& args) {
	for (auto flo : ass->floating) {
		if (needed.find(flo->var()) == needed.end()) {
			args.remove(flo->index);
		}
	}
}

static smm::Proof* translate_proof(const Maps& maps, const Proof* mproof) {
	smm::Proof* sproof = new smm::Proof();
	for (auto& node : mproof->refs) {
		Ref::Value val = node.val;
		switch (node.type) {
		case Ref::FLOATING:
			if (maps.floatings.find(val.flo) != maps.floatings.end())
				sproof->refs.push_back(smm::Ref(maps.floatings.find(val.flo)->second));
			else
				sproof->refs.push_back(smm::Ref(maps.inners.find(val.flo)->second));
			break;
		case Ref::ESSENTIAL:
			sproof->refs.push_back(smm::Ref(maps.essentials.find(val.ess)->second)); break;
		case Ref::AXIOM:
			sproof->refs.push_back(smm::Ref(maps.axioms.find(val.ax)->second, true)); break;
		case Ref::THEOREM:
			sproof->refs.push_back(smm::Ref(maps.theorems.find(val.th)->second, false)); break;
		default : assert(false && "impossible"); break;
		}
	}
	return sproof;
}

static void reduce(Maps& maps, smm::Assertion* ass, ArgMap& args, const Proof* proof) {
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

smm::Proof* transform_proof(const Maps& maps, const set<uint>& red, const Proof* proof) {
	Proof* tree = to_tree(proof);
	if (tree == nullptr)
		return nullptr;
	reduce(tree, red);
	transform(tree, maps.transform);
	Proof* rpn = to_rpn(tree);
	smm::Proof* pr = translate_proof(maps, rpn);
	delete tree;
	delete rpn;
	return pr;
}

struct Header {
	deque<Variables*>  vars;
	deque<Disjointed*> disj;
	deque<Floating*>   flos;
	deque<Essential*>  esss;
	deque<Node>        args;
};

static void gather(uint ind, const Block* block, Header& header) {
	for (int i = ind - 1; i >= 0; -- i) {
		switch (block->contents[i].type) {
		case Node::VARIABLES:
			header.vars.push_front(block->contents[i].val.var);
			break;
		case Node::DISJOINTED:
			header.disj.push_front(block->contents[i].val.dis);
			break;
		case Node::FLOATING:
			header.flos.push_front(block->contents[i].val.flo);
			header.args.push_front(block->contents[i]);
			break;
		case Node::ESSENTIAL:
			header.esss.push_front(block->contents[i].val.ess);
			header.args.push_front(block->contents[i]);
			break;
		default : break;
		}
	}
	if (block->parent) gather(block->ind, block->parent, header);
}

static void add(Maps& maps, const Header& header, smm::Assertion* ass) {
	for (auto var : header.vars)
		ass->variables.push_back(new smm::Variables { var->expr });
	for (auto dis : header.disj)
		ass->disjointed.push_back(new smm::Disjointed { dis->expr });
	for (auto ess : header.esss) {
		ass->essential.push_back(new smm::Essential {ess->label, ess->expr });
		maps.essentials[ess] = ass->essential.back();
	}
	for (auto flo : header.flos) {
		ass->floating.push_back(new smm::Floating {flo->label, flo->expr });
		maps.floatings[flo] = ass->floating.back();
	}
}

static ArgMap arg_map(const deque<Node>& ar_orig) {
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

static smm::Assertion* translate_ass(Maps& maps, const Node& n, const Block* block)  {
	smm::Assertion* ass = new smm::Assertion();
	static set<uint> red;
	ass->prop = smm::Proposition {n.type == Node::AXIOM, n.label(), n.expr()};
	Header header;
	gather(n.ind, block, header);
	add(maps, header, ass);
	ArgMap args = arg_map(header.args);
	reduce(maps, ass, args, n.proof());
	n.arity() = ass->essential.size() + ass->floating.size();
	if (n.type == Node::THEOREM) {
		ass->proof = transform_proof(maps, red, n.val.th->proof);
		if (!ass->proof) {
			// Dummy (redundant) theorem
			red.insert(n.label());
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

static void translate_block(Maps& maps, const Block* source, smm::Source* target);

static void translate_node(Maps& maps, const Node& node, const Block* block, smm::Source* target) {
	switch(node.type) {
	case Node::CONSTANTS: {
		smm::Constants* c = new smm::Constants { node.val.cst->expr };
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::THEOREM:
	case Node::AXIOM: {
		smm::Assertion* ass = translate_ass(maps, node, block);
		if (ass) target->contents.push_back(smm::Node(ass));
	} break;
	case Node::BLOCK:
		node.val.blk->ind = node.ind;
		translate_block(maps, node.val.blk, target);
		break;
	case Node::VARIABLES:  break;
	case Node::DISJOINTED: break;
	case Node::FLOATING:   break;
	case Node::ESSENTIAL:  break;
	default : assert(false && "impossible"); break;
	}
}

static void translate_block(Maps& maps, const Block* source, smm::Source* target) {
	for (auto& node : source->contents)
		translate_node(maps, node, source, target);
}

smm::Source* translate(const Block* source) {
	smm::Source* target = new smm::Source(Mm::get().config.out);
	Maps maps;
	translate_block(maps, source, target);
	return target;
}

}} // mdl::mm

