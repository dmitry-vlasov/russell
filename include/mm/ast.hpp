#pragma once

#include "mm/sys.hpp"

namespace mdl { namespace mm {

typedef mdl::Token<Source> Token;

struct Constant {
	Symbol symb;
	Token  token;
};

struct Variables {
	Vect  expr;
	Token token;
};

struct Disjointed {
	Vect  expr;
	Token token;
};

struct Essential : public Owner<Essential> {
	Essential(uint l, const Vect& e) : Owner(l), expr(e) { }
	Vect  expr;
	Token token;
};

struct Floating : public Owner<Floating> {
	Floating(uint l, const Vect& e) : Owner(l), expr(e) { }
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	Vect  expr;
	Token token;
};

struct Axiom : public Owner<Axiom> {
	Axiom(uint l, const Vect& e) : Owner(l), expr(e) { }
	Vect  expr;
	uint  arity;
	Token token;
};

class Proof;

struct Theorem : public Owner<Theorem> {
	Theorem(uint l, const Vect& e, Proof* p = nullptr) :
		Owner(l), expr(e), arity(Undef<uint>::get()), proof(p) { }
	~Theorem() override;
	Vect   expr;
	uint   arity;
	Proof* proof;
	Token  token;
};


struct Ref {
	enum Type { FLOATING, ESSENTIAL, AXIOM, THEOREM };

	Ref(uint label);
	Ref(const Ref&);
	~Ref();

	uint label() const { return label_; }
	uint arity() const {
		assert(type() == AXIOM || type() == THEOREM);
		return type() == AXIOM ?
			std::get<User<Axiom>*>(val)->get()->arity :
			std::get<User<Theorem>*>(val)->get()->arity;
	}
	Type type() const {
		return static_cast<Type>(val.index());
	}
	Floating*  flo() { return std::get<User<Floating>*>(val)->get(); }
	Essential* ess() { return std::get<User<Essential>*>(val)->get(); }
	Axiom*     axm() { return std::get<User<Axiom>*>(val)->get(); }
	Theorem*   thm() { return std::get<User<Theorem>*>(val)->get(); }

private:
	variant<
		User<Floating>*,
		User<Essential>*,
		User<Axiom>*,
		User<Theorem>*
	> val;
	uint label_;
};

struct Proof {
	Proof() = default;
	Proof(const vector<Ref*>&);
	Proof(vector<Ref*>&&);
	Proof(const Proof& p) {
		for (auto r : p.refs) refs.push_back(new Ref(*r));
	}
	~Proof();
	vector<Ref*> refs;
	Token        token;
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
		CONSTANT,
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
		Value() : ptr(nullptr) { }
		void*       ptr;
		Constant*   cst;
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

	Node()              : ind(-1), type(NONE),       val() { }
	Node(Constant* c)   : ind(-1), type(CONSTANT),  val() { val.cst = c; }
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
		case FLOATING:   return val.flo->id();
		case ESSENTIAL:  return val.ess->id();
		case AXIOM:      return val.ax->id();
		case THEOREM:    return val.th->id();
		default : assert(false && "impossible"); break;
		}
		return -1; // Pacifying compiler
	}
	Vect& expr() const {
		switch (type) {
		case FLOATING:   return val.flo->expr;
		case ESSENTIAL:  return val.ess->expr;
		case AXIOM:      return val.ax->expr;
		case THEOREM:    return val.th->expr;
		default : assert(false && "impossible"); break;
		}
		static Vect ex; return ex; // Pacifying compiler
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
	Token token;
};

struct Source : public mdl::Source<Source, Sys> {
	Source(uint l);
	~Source() override { if (block) delete block; }

	Block* block;
};

struct Inclusion {
	Inclusion(Source* src, bool prim);
	~Inclusion();
	Source* source;
	bool    primary;
	Token   token;
};

inline void Node::destroy() {
	switch(type) {
	case NONE: break;
	case CONSTANT:   delete val.cst; break;
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

ostream& operator << (ostream& os, const Node& node);
ostream& operator << (ostream& os, const Constant& cst);
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


