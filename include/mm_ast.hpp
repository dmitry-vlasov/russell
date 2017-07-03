#pragma once

#include "mm_sys.hpp"

namespace mdl { namespace mm {

typedef mdl::Token<Source> Token;

struct Tokenable {
	Tokenable(const Token& t) : token(t) { }
	virtual ~Tokenable() { }
	Token token;
};

struct Constant : public Tokenable {
	Constant(Symbol s, const Token& t = Token()) : Tokenable(t), symb(s) { }
	Symbol symb;
};

struct Variables : public Tokenable {
	Variables(const Vect& e, const Token& t = Token()) : Tokenable(t), expr(e) { }
	Vect  expr;
};

struct Disjointed : public Tokenable {
	Disjointed(const Vect& e, const Token& t = Token()) : Tokenable(t), expr(e) { }
	Vect  expr;
};

struct Essential : public Tokenable, public Owner<Essential> {
	Essential(uint l, const Vect& e, const Token& t = Token()) : Tokenable(t), Owner(l), expr(e) { }
	Vect  expr;
};

struct Floating : public Tokenable, public Owner<Floating> {
	Floating(uint l, const Vect& e, const Token& t = Token()) : Tokenable(t), Owner(l), expr(e) { }
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	Vect  expr;
};

struct Axiom : public Tokenable, public Owner<Axiom> {
	Axiom(uint l, const Vect& e, const Token& t = Token()) : Tokenable(t), Owner(l), expr(e), arity(-1) { }
	Vect  expr;
	uint  arity;
};

class Proof;

struct Theorem : public Tokenable, public Owner<Theorem> {
	Theorem(uint l, const Vect& e, Proof* p = nullptr, const Token& t = Token()) :
		Tokenable(t), Owner(l), expr(e), arity(Undef<uint>::get()), proof(p) { }
	~Theorem() override;
	Vect   expr;
	uint   arity;
	Proof* proof;
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
			val_.axm->get()->arity :
			val_.thm->get()->arity;
	}
	Type type() const { return type_; }
	bool is_assertion() const { return type_ == AXIOM || type_ == THEOREM; }
	Floating*  flo() { return val_.flo->get(); }
	Essential* ess() { return val_.ess->get(); }
	Axiom*     axm() { return val_.axm->get(); }
	Theorem*   thm() { return val_.thm->get(); }

private:
	union Value {
		Value() : flo(nullptr) { }
		User<Floating>*  flo;
		User<Essential>* ess;
		User<Axiom>*     axm;
		User<Theorem>*   thm;
	};
	Value val_;
	Type type_;
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
	Inclusion(uint src, bool prim);
	User<Source> source;
	bool         primary;
	Token        token;
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


