#pragma once

#include "smm_sys.hpp"

namespace mdl { namespace smm {

typedef mdl::Token<Source> Token;
typedef mdl::Tokenable<Source> Tokenable;

struct Constant : public Tokenable, Owner<Constant> {
	Constant (Symbol s, const Token& t = Token()) : Tokenable(t), Owner(s.lit), symb(s) { }
	Symbol symb;
};

struct Variables : public Tokenable {
	Variables(const Vect& e = Vect(), const Token& t = Token()) : Tokenable(t), expr(e) { }
	Vect expr;
};

struct Disjointed : public Tokenable {
	Disjointed(const Vect& e = Vect(), const Token& t = Token()) : Tokenable(t), expr(e) { }
	Vect expr;
};

struct Essential : public Tokenable {
	Essential(uint i, const Vect& e, const Token& t = Token()) : Tokenable(t), index(i), expr(e) { }
	uint index;
	Vect expr;
};

struct Floating : public Tokenable {
	Floating(uint i, const Vect& e = Vect(), const Token& t = Token()) : Tokenable(t), index(i), expr(e) { }
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	uint index;
	Vect expr;
};

struct Inner : public Tokenable {
	Inner(uint i, const Vect& e = Vect(), const Token& t = Token()) : Tokenable(t), index(i), expr(e) { }
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	uint index;
	Vect expr;
};

struct Proposition : public Tokenable {
	Proposition(bool ax, uint l, const Vect& e, const Token& t = Token()) :
		Tokenable(t), axiom(ax), label(l), expr(e) { }
	bool axiom;
	uint label;
	Vect expr;
};

struct Proof;

struct Assertion : public Tokenable, public Owner<Assertion> {
	Assertion (uint label, const Token& t = Token()) :
		Tokenable(t), Owner(label), prop(nullptr), proof(nullptr) { }
	~Assertion() override;

	uint arity() const {
		return essential.size() + floating.size();
	}

	vector<Variables*>  variables;
	vector<Disjointed*> disjointed;
	vector<Essential*>  essential;
	vector<Floating*>   floating;
	vector<Inner*>      inner;
	Proposition* prop;
	Proof*       proof;
};

struct Proof;

struct Ref {
	enum Type { ESSENTIAL, FLOATING, INNER, AXIOM, THEOREM };

	Ref(Floating* f)  : type_(FLOATING)  { val_.flo = f; }
	Ref(Essential* e) : type_(ESSENTIAL) { val_.ess = e; }
	Ref(Inner* i)     : type_(INNER)     { val_.inn = i; }
	Ref(uint label, bool ax);
	Ref(const Ref& ref);
	~Ref();

	void operator=(const Ref&) = delete;

	Type type() const { return type_; }
	bool is_assertion() const { return type_ == THEOREM || type_ == AXIOM; }
	Floating*  flo() { return val_.flo; }
	Essential* ess() { return val_.ess; }
	Inner*     inn() { return val_.inn; }
	Assertion* ass() { return val_.ass->get(); }

	uint label() const {
		assert(is_assertion() && "must be assertion");
		return val_.ass->get()->prop->label;
	}
	uint index() const {
		assert(!is_assertion() && "must not be assertion");
		switch (type_) {
		case ESSENTIAL : return val_.ess->index;
		case FLOATING  : return val_.flo->index;
		case INNER     : return val_.inn->index;
		default : assert(false && "must not be assertion"); return -1;
		}
	}

private:
	union Value {
		Value() : flo(nullptr) { }
		Floating*        flo;
		Essential*       ess;
		Inner*           inn;
		User<Assertion>* ass;
	};
	Type type_;
	Value val_;
};

struct Proof {
	Proof() : theorem(nullptr) { }
	Proof(const Proof& p) : theorem(p.theorem) {
		for (auto r : p.refs) refs.push_back(new Ref(*r));
	}
	~ Proof();
	vector<Ref*> refs;
	Assertion*   theorem;
	Token        token;
};

struct Comment {
	Comment(const string& t) : text(t) { }
	string text;
};

class Source;

struct Inclusion {
	Inclusion(uint s, bool p) : source(s), primary(p) { }
	User<Source> source;
	bool         primary;
	Token        token;
};

struct Node {
	Node() : type(NONE), val() { }
	Node(Assertion* a) : type (ASSERTION), val() { val.ass = a; }
	Node(Constant* c)  : type (CONSTANT), val() { val.cst = c; }
	Node(Inclusion* i) : type (INCLUSION), val() { val.inc = i; }
	Node(Comment* c)   : type (COMMENT),   val() { val.com = c; }
	void destroy();

	enum Type {
		NONE,
		ASSERTION,
		CONSTANT,
		INCLUSION,
		COMMENT
	};
	Type type;
	union Value {
		Value() : ptr(nullptr) { }
		void*      ptr;
		Assertion* ass;
		Constant*  cst;
		Inclusion* inc;
		Comment*   com;
	};
	Value val;
};

struct Source : public mdl::Source<Source, Sys> {
	Source(uint l);
	~ Source();

	vector<Node> contents;
};

inline void Node::destroy() {
	switch(type) {
	case NONE: break;
	case ASSERTION: delete val.ass; break;
	case CONSTANT:  delete val.cst; break;
	case INCLUSION: delete val.inc; break;
	case COMMENT:   delete val.com; break;
	default : assert(false && "impossible");  break;
	}
	type = NONE;
}

inline Proof::~ Proof() {
	for (auto r : refs) delete r;
}

typedef map<Symbol, Vect> Subst;
Vect apply(const Subst& sub, const Vect& expr);

ostream& operator << (ostream& os, const Constant& cst);
ostream& operator << (ostream& os, const Ref& ref);
ostream& operator << (ostream& os, const Proof& proof);
ostream& operator << (ostream& os, const Variables& vars);
ostream& operator << (ostream& os, const Disjointed& disj);
ostream& operator << (ostream& os, const Essential& ess);
ostream& operator << (ostream& os, const Floating& flo);
ostream& operator << (ostream& os, const Inner& inn);
ostream& operator << (ostream& os, const Proposition& prop);
ostream& operator << (ostream& os, const Assertion& ass);
ostream& operator << (ostream& os, const Node& node);
ostream& operator << (ostream& os, const Source& src);
ostream& operator << (ostream& os, const Comment& com);
ostream& operator << (ostream& os, const Inclusion& inc);

}} // mdl::smm


