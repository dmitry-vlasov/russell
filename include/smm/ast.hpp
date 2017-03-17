#pragma once

#include <boost/algorithm/string.hpp>

#include "common.hpp"

namespace mdl { namespace smm {

struct Constants {
	Vect expr;
};

struct Variables {
	Vect expr;
};

struct Disjointed {
	Vect expr;
};

struct Essential {
	uint index;
	Vect expr;
};

struct Floating  {
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	uint index;
	Vect expr;
};

struct Inner {
	Symbol type() const { return expr[0]; }
	Symbol var() const { return expr[1]; }
	uint index;
	Vect expr;
};

struct Proposition {
	bool axiom;
	uint label;
	Vect expr;
};

struct Proof;

struct Assertion {
	Assertion (uint label);
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
		Value() : ptr(nullptr) { }
		void*       ptr;
		Floating*   flo;
		Essential*  ess;
		Inner*      inn;
		Assertion*  ass;
		Proof*      prf;
	};
	Ref(Floating* f)  : type(FLOATING),   val() { val.flo = f; }
	Ref(Essential* e) : type(ESSENTIAL),  val() { val.ess = e; }
	Ref(Inner* i)     : type(INNER),      val() { val.inn = i; }
	Ref(uint label, bool ax);
	Ref(Proof* p)     : type(PROOF),      val() { val.prf = p; }
	Ref(const Ref& ref);
	~Ref();

	void operator=(const Ref&) = delete;

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
	Vect expr;
};

struct Proof {
	enum Type {
		TREE,
		RPN
	};
	Proof(Type tp = RPN) : refs(), theorem(nullptr), type(tp) { }
	Proof(const Proof& p) : refs(), theorem(p.theorem), type(p.type) {
		for (auto r : p.refs) refs.push_back(new Ref(*r));
	}
	~ Proof();
	vector<Ref*> refs;
	Assertion*   theorem;
	Type         type;
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

struct Source {
	Source(uint l);
	~ Source();
	uint   label;
	string data;

	Path rich_path() const;

	string name() const { return Lex::toStr(label); }
	string dir() const { return rich_path().dir(); }
	string path() const { return rich_path().path(); }

	void read();
	void write();

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

inline Ref::Ref(const Ref& ref) : type(ref.type), val() {
	val.ptr = (type == PROOF) ? new Proof(*ref.val.prf) : ref.val.ptr;
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
ostream& operator << (ostream& os, const Inclusion& inc);

}} // mdl::smm


