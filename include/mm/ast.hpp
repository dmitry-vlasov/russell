#pragma once

#include <boost/algorithm/string.hpp>

#include "common.hpp"

namespace mdl { namespace mm {

struct Constants {
	Expr expr;
};

struct Variables {
	Expr expr;
};

struct Disjointed {
	Expr expr;
};

struct Essential {
	uint label;
	Expr expr;
};

struct Floating  {
	Symbol type() const { return expr.symbols[0]; }
	Symbol var() const { return expr.symbols[1]; }
	uint label;
	Expr expr;
};

struct Axiom {
	uint label;
	Expr expr;
	uint arity;
};

class Proof;

struct Theorem {
	Theorem() : label(-1), expr(), arity(0), proof(nullptr) { }
	~Theorem();
	uint   label;
	Expr   expr;
	uint   arity;
	Proof* proof;
};


struct Ref {
	enum Type {
		NONE,
		FLOATING,
		ESSENTIAL,
		AXIOM,
		THEOREM,
		PROOF
	};
	union Value {
		void*       non;
		Floating*   flo;
		Essential*  ess;
		Axiom*      ax;
		Theorem*    th;
		Proof*      prf;
	};

	Ref()              : type(NONE),       val() { val.non = nullptr; }
	Ref(Floating* f)   : type(FLOATING),   val() { val.flo = f; }
	Ref(Essential* e)  : type(ESSENTIAL),  val() { val.ess = e; }
	Ref(Axiom* a)      : type(AXIOM),      val() { val.ax  = a; }
	Ref(Theorem* t)    : type(THEOREM),    val() { val.th  = t; }
	Ref(Proof* p)      : type(PROOF),      val() { val.prf = p; }
	void destroy();

	uint label() const {
		switch (type) {
		case FLOATING:   return val.flo->label;
		case ESSENTIAL:  return val.ess->label;
		case AXIOM:      return val.ax->label;
		case THEOREM:    return val.th->label;
		default : assert(false && "impossible"); break;
		}
		return -1; // Pacifying compiler
	}
	uint arity() const {
		assert(type == AXIOM || type == THEOREM);
		return type == AXIOM ? val.ax->arity : val.th->arity;
	}

	Type type;
	Value val;
};


struct Proof {
	enum Type {
		TREE,
		RPN
	};
	Proof(Type t = RPN) : refs(), type(t) { }
	~Proof();
	vector<Ref> refs;
	Type        type;
};


struct Comment {
	Comment(string t) : text(t) { }
	string text;
};

class Block;
class Source;
class Inclusion;

struct Node {
	enum Type {
		NONE,
		CONSTANTS,
		VARIABLES,
		DISJOINTED,
		FLOATING,
		ESSENTIAL,
		AXIOM,
		THEOREM,
		BLOCK,
		SOURCE,
		INCLUSION,
		COMMENT
	};
	union Value {
		void*       non;
		Constants*  cst;
		Variables*  var;
		Disjointed* dis;
		Floating*   flo;
		Essential*  ess;
		Axiom*      ax;
		Theorem*    th;
		Block*      blk;
		Source*     src;
		Inclusion*  inc;
		Comment*    com;
	};

	Node()              : ind(-1), type(NONE),       val() { val.non = nullptr; }
	Node(Constants* c)  : ind(-1), type(CONSTANTS),  val() { val.cst = c; }
	Node(Variables* v)  : ind(-1), type(VARIABLES),  val() { val.var = v; }
	Node(Disjointed* d) : ind(-1), type(DISJOINTED), val() { val.dis = d; }
	Node(Floating* f)   : ind(-1), type(FLOATING),   val() { val.flo = f; }
	Node(Essential* e)  : ind(-1), type(ESSENTIAL),  val() { val.ess = e; }
	Node(Axiom* a)      : ind(-1), type(AXIOM),      val() { val.ax  = a; }
	Node(Theorem* t)    : ind(-1), type(THEOREM),    val() { val.th  = t; }
	Node(Block* b)      : ind(-1), type(BLOCK),      val() { val.blk = b; }
	Node(Source* s)     : ind(-1), type(SOURCE),     val() { val.src = s; }
	Node(Inclusion* i)  : ind(-1), type(INCLUSION),  val() { val.inc = i; }
	Node(Comment* c)    : ind(-1), type(COMMENT),    val() { val.com = c; }

	void destroy();

	uint label() const {
		switch (type) {
		case FLOATING:   return val.flo->label;
		case ESSENTIAL:  return val.ess->label;
		case AXIOM:      return val.ax->label;
		case THEOREM:    return val.th->label;
		default : assert(false && "impossible"); break;
		}
		return -1; // Pacifying compiler
	}
	Expr& expr() const {
		switch (type) {
		case FLOATING:   return val.flo->expr;
		case ESSENTIAL:  return val.ess->expr;
		case AXIOM:      return val.ax->expr;
		case THEOREM:    return val.th->expr;
		default : assert(false && "impossible"); break;
		}
		static Expr ex; return ex; // Pacifying compiler
	}
	const Proof* proof() const {
		assert(type == AXIOM || type == THEOREM);
		return type == AXIOM ? nullptr : val.th->proof;
	}
	uint& arity() const {
		assert(type == AXIOM || type == THEOREM);
		return type == AXIOM ? val.ax->arity : val.th->arity;
	}

	uint ind;
	Type type;
	Value val;
};


struct Block {
	Block(): ind(-1), parent(nullptr), sibling(nullptr), contents() { }
	Block(Block* p) : ind(-1), parent(p), sibling(nullptr), contents() { }
	~ Block() {
		for (auto& node : contents)
			node.destroy();
	}
	uint ind;
	Block* parent;
	Block* sibling;
	vector<Node> contents;
};

struct Source {
	Source(const string& r, const string& n) : root(r), name(n), block(new Block) {
		boost::erase_last(name, ".mm");
	}
	string root;
	string name;
	string path() { return (root.size() ? root + "/" + name : name) + ".mm"; }
	string dir() { string p = path(); return p.substr(0, p.find_last_of("/")) + "/"; }
	Block* block;
};

struct Inclusion {
	Inclusion(Source* src, bool prim) : source(src), primary(prim) { }
	~ Inclusion() { if (primary && source) delete source; }
	Source* source;
	bool primary;
};

inline Theorem::~Theorem() {
	if (proof)
		delete proof;
}

inline void Node::destroy() {
	switch(type) {
	case NONE: break;
	case CONSTANTS:  delete val.cst; break;
	case VARIABLES:  delete val.var; break;
	case DISJOINTED: delete val.dis; break;
	case FLOATING:   delete val.flo; break;
	case ESSENTIAL:  delete val.ess; break;
	case AXIOM:      delete val.ax;  break;
	case THEOREM:    delete val.th;  break;
	case BLOCK:      delete val.blk; break;
	case SOURCE:     delete val.src; break;
	case INCLUSION:  delete val.inc; break;
	case COMMENT:    delete val.com; break;
	default : assert(false && "impossible"); break;
	}
	type = NONE;
}

inline Proof::~Proof() {
	if (type == TREE) {
		for (auto& r : refs) {
			if (r.type == Ref::PROOF) {
				delete r.val.prf;
			}
		}
	}
}

ostream& operator << (ostream& os, const Node& node);
ostream& operator << (ostream& os, const Constants& cst);
ostream& operator << (ostream& os, const Ref& ref);
ostream& operator << (ostream& os, const Proof& proof);
ostream& operator << (ostream& os, const Variables& vars);
ostream& operator << (ostream& os, const Variables& disj);
ostream& operator << (ostream& os, const Essential& ess);
ostream& operator << (ostream& os, const Floating& flo);
ostream& operator << (ostream& os, const Axiom& ax);
ostream& operator << (ostream& os, const Theorem& th);
ostream& operator << (ostream& os, const Block& block);
ostream& operator << (ostream& os, const Source& source);
ostream& operator << (ostream& os, const Inclusion& inc);
ostream& operator << (ostream& os, const Comment& com);

}} // mdl::mm


