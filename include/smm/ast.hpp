#pragma once

#include "common.hpp"

namespace mdl { namespace smm {

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
	uint index;
	Expr expr;
};

struct Floating  {
	Symbol type() const { return expr.symbols[0]; }
	Symbol var() const { return expr.symbols[1]; }
	uint index;
	Expr expr;
};

struct Inner {
	Symbol type() const { return expr.symbols[0]; }
	Symbol var() const { return expr.symbols[1]; }
	uint index;
	Expr expr;
};

struct Proposition {
	bool axiom;
	uint label;
	Expr expr;
};

struct Proof;

struct Assertion {
	Assertion ();
	~Assertion();

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
	Location    loc;
};

struct Proof;

struct Ref {
	enum Type {
		NONE,
		ESSENTIAL,
		FLOATING,
		INNER,
		AXIOM,
		THEOREM,
		PROOF
	};
	union Value {
		void*       non;
		Floating*   flo;
		Essential*  ess;
		Inner*      inn;
		Assertion*  ass;
		Proof*      prf;
	};
	Ref() : type(NONE), val() { val.non = nullptr; }
	Ref(Floating* f)  : type(FLOATING),  val() { val.flo = f; }
	Ref(Essential* e) : type(ESSENTIAL), val() { val.ess = e; }
	Ref(Inner* i)     : type(INNER),     val() { val.inn = i; }
	Ref(Assertion* a, bool ax) : type(ax ? AXIOM : THEOREM), val() { val.ass = a; }
	Ref(Proof* p)     : type(PROOF),     val() { val.prf = p; }
	void destroy();

	uint label() const {
		assert(type == THEOREM || type == AXIOM);
		return val.ass->prop.label;
	}
	uint index() const {
		switch (type) {
		case ESSENTIAL : return val.ess->index;
		case FLOATING  : return val.flo->index;
		case INNER     : return val.inn->index;
		default : assert(false && "impossible");
		}
		return -1; // pacify compiler
	}

	Type type;
	Value val;
	Expr expr;
};

struct Proof {
	enum Type {
		TREE,
		RPN
	};
	Proof(Type tp = RPN) : refs(), theorem(nullptr), type(tp) { }
	~ Proof();
	vector<Ref> refs;
	Assertion*  theorem;
	Type        type;
};

struct Comment {
	Comment(const string& t) : text(t) { }
	string text;
};

class Source;

struct Node {
	Node() : type(NONE), val() { val.non = nullptr; }
	Node(Assertion* a) : type (ASSERTION), val() { val.ass = a; }
	Node(Constants* c) : type (CONSTANTS), val() { val.cst = c; }
	Node(Source* s)    : type (SOURCE),    val() { val.src = s; }
	Node(Comment* c)   : type (COMMENT),   val() { val.com = c; }
	void destroy();

	enum Type {
		NONE,
		ASSERTION,
		CONSTANTS,
		SOURCE,
		COMMENT
	};
	Type type;
	union Value {
		void*      non;
		Assertion* ass;
		Constants* cst;
		Source*    src;
		Comment*   com;
	};
	Value val;
};

struct Source {
	Source(const string& n) :
	top(false), name(n), contents() {
		static bool t = true; top = t; t = false;
	}
	~ Source() {
		for (auto& node : contents)
			node.destroy();
	}

	bool   top;
	string name;
	vector<Node> contents;
};


inline Assertion::Assertion() :
	variables(), disjointed(), essential(),
	floating(), inner(),
	prop(), proof(), loc() {
}
inline Assertion::~Assertion() {
	for (Variables* v : variables)   delete v;
	for (Disjointed* d : disjointed) delete d;
	for (Essential* e : essential)   delete e;
	for (Floating* f : floating)     delete f;
	for (Inner* i : inner)           delete i;
	if (proof) delete proof;
}

inline void Node::destroy() {
	switch(type) {
	case NONE: break;
	case ASSERTION: delete val.ass; break;
	case CONSTANTS: delete val.cst; break;
	case SOURCE:    delete val.src; break;
	default : assert(false && "impossible");  break;
	}
	type = NONE;
}

inline void Ref::destroy() {
	if (type == PROOF)
		delete val.prf;
}

inline Proof::~ Proof() {
	for (auto& r : refs)
		r.destroy();
}

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

}} // mdl::smm


