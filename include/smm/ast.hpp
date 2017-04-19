#pragma once

#include "smm/sys.hpp"

namespace mdl { namespace smm {

typedef mdl::Token<Source> Token;

struct Constants {
	Vect  expr;
	Token token;
};

struct Variables {
	Vect  expr;
	Token token;
};

struct Disjointed {
	Vect  expr;
	Token token;
};

struct Essential {
	uint  index;
	Vect  expr;
	Token token;
};

struct Floating  {
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	uint  index;
	Vect  expr;
	Token token;
};

struct Inner {
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	uint  index;
	Vect  expr;
	Token token;
};

struct Proposition {
	bool  axiom;
	uint  label;
	Vect  expr;
	Token token;
};

struct Proof;

struct Assertion : public Owner<Assertion> {
	Assertion (uint label) : Owner(label), proof(nullptr) { }
	~Assertion() override;

	uint arity() const {
		return essential.size() + floating.size();
	}

	vector<Variables*>  variables;
	vector<Disjointed*> disjointed;
	vector<Essential*>  essential;
	vector<Floating*>   floating;
	vector<Inner*>      inner;
	Proposition prop;
	Proof*      proof;
	Token       token;
};

struct Proof;

struct Ref {
	enum Type {
		ESSENTIAL,
		FLOATING,
		INNER,
		AXIOM,
		THEOREM
	};
	union Value {
		Value() : flo(nullptr) { }
		Floating*   flo;
		Essential*  ess;
		Inner*      inn;
		Assertion*  ass;
	};
	Ref(Floating* f)  : type(FLOATING)  { val.flo = f; }
	Ref(Essential* e) : type(ESSENTIAL) { val.ess = e; }
	Ref(Inner* i)     : type(INNER)     { val.inn = i; }
	Ref(uint label, bool ax);
	Ref(const Ref& ref);
	~Ref();

	void operator=(const Ref&) = delete;

	bool is_assertion() const {
		return type == THEOREM || type == AXIOM;
	}

	uint label() const {
		assert(is_assertion() && "must be assertion");
		return val.ass->prop.label;
	}
	uint index() const {
		assert(!is_assertion() && "must not be assertion");
		switch (type) {
		case ESSENTIAL : return val.ess->index;
		case FLOATING  : return val.flo->index;
		case INNER     : return val.inn->index;
		}
		return -1; // pacify compiler
	}

	Type type;
	Value val;
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
	Inclusion(Source* s, bool p) : source(s), primary(p) { }
	Source* source;
	bool    primary;
	Token   token;
};

struct Node {
	Node() : type(NONE), val() { }
	Node(Assertion* a) : type (ASSERTION), val() { val.ass = a; }
	Node(Constants* c) : type (CONSTANTS), val() { val.cst = c; }
	Node(Inclusion* i) : type (INCLUSION), val() { val.inc = i; }
	Node(Comment* c)   : type (COMMENT),   val() { val.com = c; }
	void destroy();

	enum Type {
		NONE,
		ASSERTION,
		CONSTANTS,
		INCLUSION,
		COMMENT
	};
	Type type;
	union Value {
		Value() : ptr(nullptr) { }
		void*      ptr;
		Assertion* ass;
		Constants* cst;
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
	case CONSTANTS: delete val.cst; break;
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

ostream& operator << (ostream& os, const Constants& cst);
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


