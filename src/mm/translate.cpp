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
	for (Node n : proof->refs) {
		if (n.type == Node::FLOATING) {
			Symbol v = n.val.flo->var();
			avars.insert(v);
			if (fvars.find(v) == fvars.end())
				ivars.insert(v);
		}
	}
}

typedef map<uint, uint> Reindex;

// Replace variable sets with single set, which contains only needed variables.
//
static void reduce_variables(smm::Assertion* ass, const set<Symbol>& needed) {
	Expr rvars;
	for (const smm::Variables& vars : ass->variables) {
		for (Symbol v : vars.expr.symbols) {
			if (needed.find(v) != needed.end())
				rvars += v;
		}
	}
	ass->variables.clear();
	ass->variables.push_back(smm::Variables { rvars });
}

// Remove floatings, which variable is not needed.
//
static void reduce_floatings(smm::Assertion* ass, const set<Symbol>& needed, Reindex& reindex) {
	vector<smm::Floating> red_flos;
	uint i = 0;
	for (auto& flo : ass->floating) {
		if (needed.find(flo.var()) != needed.end()) {
			reindex[flo.index] = i;
			flo.index = i++;
			red_flos.push_back(flo);
		}
	}
	ass->floating = red_flos;
}

struct Arg {
	uint label;
	uint ind;
};

class ArgMap;

ostream& operator << (ostream& os, const ArgMap& amap);

struct ArgMap {
	typedef vector<Arg>::iterator Iter;

	uint index(Iter a, Iter b) {
		return b - a;
	}

	Perm create_permutation() {
		Perm perm;
		for (uint i = 0; i < args.size(); ++ i)
			perm[i] = args[i].ind;
		return perm;
	}
	void remove(uint label) {
		ArgMap before = *this;
		Iter found = args.end();
		Iter begin = args.begin();
		for (auto it = begin; it != args.end(); ++ it) {
			if (it->ind > found - begin)
				-- it->ind;
			if (it->label == label)
				found = it;
		}
		if (found != args.end()) {
			args.erase(found);
			//cout << "before: " << endl << before << endl;
			//cout << "after: " << endl << *this << endl;
		}
	}
	Arg& operator [] (uint i) {
		return args[i];
	}
	vector<Arg> args;
};

ostream& operator << (ostream& os, const ArgMap& amap) {
	for (uint i = 0; i < amap.args.size(); ++ i) {
		Arg arg = amap.args[i];
		os << label(arg.label) << ": " << i << " -> " << arg.ind << endl;
	}
	return os;
}
ostream& operator << (ostream& os, const Perm& perm) {
	for (auto& p : perm) {
		os << p.first << " -> " << p.second << endl;
	}
	return os;
}

// Reduce permutation, remove variable which are not needed.
//
static void reduce_permutation(smm::Assertion* ass, const set<Symbol>& needed, ArgMap& args) {
	for (auto& flo : ass->floating) {
		if (needed.find(flo.var()) == needed.end()) {
			args.remove(flo.index);
		}
	}
}

// Reindex essentials.
//
static void reindex_essentials(smm::Assertion* ass, Reindex& reindex) {
	uint i = 0;
	for (auto& ess : ass->essential) {
		reindex[ess.index] = i;
		ess.index = i++;
	}
}

static smm::Proof* translate(Proof* mproof, Reindex& reindex) {
	typedef smm::Ref::Type RType;
	smm::Proof* sproof = new smm::Proof();
	for (auto& node : mproof->refs) {
		smm::Ref sref;
		Node::Value val = node.val;
		switch (node.type) {
		case Node::FLOATING:  sref = smm::Ref { RType::PREF_F, reindex[val.flo->label] }; break;
		case Node::ESSENTIAL: sref = smm::Ref { RType::PREF_E, reindex[val.ess->label] }; break;
		case Node::AXIOM:     sref = smm::Ref { RType::PREF_A, val.ax->label };  break;
		case Node::THEOREM:   sref = smm::Ref { RType::PREF_P, val.th->label };  break;
		default : assert(false && "impossible"); break;
		}
		sproof->refs.push_back(sref);
	}
	return sproof;
}


static void reduce(Transform& trans, smm::Assertion* ass, ArgMap& args, Proof* proof = nullptr) {
	// Gather the variables, used in assertion hypotheses and statement (header).
	set<Symbol> flo_vars;
	for (auto& ess : ass->essential) {
		gather_expr_vars(flo_vars, ess.expr);
	}
	gather_expr_vars(flo_vars, ass->prop.expr);

	// Gather the variables, used in proof but not in header, and collect all vars.
	set<Symbol> inn_vars;
	set<Symbol> all_vars(flo_vars);
	gather_inner_vars(flo_vars, inn_vars, all_vars, proof);

	Reindex reindex;
	reduce_variables(ass, all_vars);
	reduce_permutation(ass, flo_vars, args);
	reduce_floatings(ass, flo_vars, reindex);
	reindex_essentials(ass, reindex);
	if (proof) {
		//cout << "orig: " << endl << *proof << endl;
		Proof* tree = to_tree(proof);
		//cout << "tree: " << endl << *tree << endl;
		transform(tree, trans);
		//cout << "transform: " << endl << *tree << endl;
		Proof* rpn = to_rpn(tree);
		//cout << "rpn: " << endl << *rpn << endl;
		ass->proof = translate(rpn, reindex);
		delete tree;
		delete rpn;
	}
	//cout << args << endl;
	//cout << args.create_permutation() << endl;
	trans[ass->prop.label] = args.create_permutation();
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

inline uint hyp_label(const Node& node) {
	return node.type == Node::FLOATING ? node.val.flo->label : node.val.ess->label;
}

static void add(const Header& header, smm::Assertion* ass) {
	for (auto var : header.vars)
		ass->variables.push_back(smm::Variables { var->expr });
	for (auto dis : header.disj)
		ass->disjointed.push_back(smm::Disjointed { dis->expr });
	for (auto ess : header.esss)
		ass->essential.push_back(smm::Essential {ess->label, ess->expr });
	for (auto flo : header.flos)
		ass->floating.push_back(smm::Floating {flo->label, flo->expr });
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
			a_map.args.push_back(Arg { n.val.ess->label, ess_ind ++});
		else if (n.type == Node::FLOATING)
			a_map.args.push_back(Arg { n.val.flo->label, ess_num + flo_ind ++});
		else
			assert(false && "impossible");
	}
	return a_map;
}

static void translate(Transform& trans, const Block* source, smm::Source* target);

static void translate(Transform& trans, const Node& node, const Block* block, smm::Source* target) {
	switch(node.type) {
	case Node::NONE: assert(false && "impossible"); break;;
	case Node::CONSTANTS: {
		smm::Constants* c = new smm::Constants { node.val.cst->expr };
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::VARIABLES:  break;
	case Node::DISJOINTED: break;
	case Node::FLOATING:   break;
	case Node::ESSENTIAL:  break;
	case Node::AXIOM: {
		smm::Assertion* ass = new smm::Assertion();
		ass->prop = smm::Proposition { true, node.val.ax->label, node.val.ax->expr };
		Header header;
		gather(node.ind, block, header);
		add(header, ass);
		ArgMap args = arg_map(header.args);
		reduce(trans, ass, args);
		node.val.ax->arity = ass->essential.size() + ass->floating.size();
		target->contents.push_back(smm::Node(ass));
	} break;
	case Node::THEOREM: {
		smm::Assertion* th = new smm::Assertion();
		th->prop = smm::Proposition { false, node.val.th->label, node.val.th->expr };
		Header header;
		gather(node.ind, block, header);
		add(header, th);
		ArgMap args = arg_map(header.args);
		reduce(trans, th, args, node.val.th->proof);
		node.val.th->arity = th->essential.size() + th->floating.size();
		target->contents.push_back(smm::Node(th));
	}	break;
	case Node::BLOCK:
		node.val.blk->ind = node.ind;
		translate(trans, node.val.blk, target);
		break;
	default : assert(false && "impossible"); break;
	}
}

static void translate(Transform& trans, const Block* source, smm::Source* target) {
	for (auto& node : source->contents)
		translate(trans, node, source, target);
}

smm::Source* translate(const Block* source) {
	smm::Source* target = new smm::Source(Mm::get().config.out);
	Transform trans;
	translate(trans, source, target);
	return target;
}

}} // mdl::mm

