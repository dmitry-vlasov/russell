/*****************************************************************************/
/* Project name:    smm - verifier for the Simplified MetaMath language      */
/* File Name:       smm_ast_Source.hpp                                       */
/* Description:     smm source                                               */
/* Copyright:       (c) 2006-2010 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

#pragma once

#include "common.hpp"

namespace mdl { namespace smm {

struct Constants {
	Expr expr;
};

struct Ref {
	enum Type {
		PREF_E, ///< "e"
		PREF_F, ///< "f"
		PREF_I, ///< "i"
		PREF_A, ///< "a"
		PREF_P  ///< "p"
	};
	Type type;
	uint index;
};

struct Proof {
	vector<Ref> refs;
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
	const Symbol& type() const { return expr.symbols[0]; }
	const Symbol& var() const { return expr.symbols[1]; }
	uint index;
	Expr expr;
};

struct Inner {
	uint index;
	Expr expr;
};

struct Proposition {
	bool axiom;
	uint label;
	Expr expr;
};

struct Assertion {
	Assertion () :
	variables(), disjointed(), essential(),
	floating(), inner(),
	prop(), proof(nullptr), loc() { }
	~Assertion() {
		if (proof) delete proof;
	}

	bool areDisjointed(Symbol s1, Symbol s2) const {
		for (auto it = disjointed.cbegin(); it != disjointed.cend(); ++ it) {
			if (it->expr.contains(s1) && it->expr.contains(s2))
				return true;
		}
		return false;
	}

	vector<Variables>  variables;
	vector<Disjointed> disjointed;
	vector<Essential>  essential;
	vector<Floating>   floating;
	vector<Inner>      inner;
	Proposition        prop;
	Proof*             proof;
	Location           loc;
};

class Source;

struct Node {
	Node() : type(NONE), val() { val.non = nullptr; }
	Node(Assertion* a) : type (ASSERTION), val() { val.ass = a; }
	Node(Constants* c) : type (CONSTANTS), val() { val.cst = c; }
	Node(Source* s)    : type (SOURCE),    val() { val.src = s; }
	void destroy();

	enum Type {
		NONE,
		ASSERTION,
		CONSTANTS,
		SOURCE
	};
	Type type;
	union Value {
		void*      non;
		Assertion* ass;
		Constants* cst;
		Source*    src;
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

ostream& operator << (ostream& os, const Constants& cst);
ostream& operator << (ostream& os, const Ref& ref);
ostream& operator << (ostream& os, const Proof& proof);
ostream& operator << (ostream& os, const Variables& vars);
ostream& operator << (ostream& os, const Variables& disj);
ostream& operator << (ostream& os, const Essential& ess);
ostream& operator << (ostream& os, const Floating& flo);
ostream& operator << (ostream& os, const Inner& inn);
ostream& operator << (ostream& os, const Proposition& prop);
ostream& operator << (ostream& os, const Assertion& ass);
ostream& operator << (ostream& os, const Node& node);
ostream& operator << (ostream& os, const Source& src);

}} // mdl::smm


