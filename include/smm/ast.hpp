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

struct Constants : public Showable {
	virtual void show (string& str) const;
	Expr expr;
};

struct Ref : public Showable {
public :
	enum Type {
		PREF_E, ///< "e"
		PREF_F, ///< "f"
		PREF_I, ///< "i"
		PREF_A, ///< "a"
		PREF_P  ///< "p"
	};
	virtual void show (string& str) const;
	Type type;
	uint index;
};

class Assertion;

class Proof : public Showable {
public :
	virtual void show (string& str) const;
	vector<Ref> refs;
};


struct Variables : public Showable {
	virtual void show (string& str) const;
	Expr expr;
};


struct Disjointed : public Showable {
	virtual void show (string& str) const;
	Expr expr;
};

struct Essential : public Showable {
	virtual void show (string& str) const;
	uint index;
	Expr expr;
};

struct Floating : public Showable {
	const Symbol& type() const { return expr.symbols[0]; }
	const Symbol& var() const { return expr.symbols[1]; }
	virtual void show (string& str) const;
	uint index;
	Expr expr;
};

struct Inner : public Showable {
	virtual void show (string& str) const;
	uint index;
	Expr expr;
};

struct Proposition : public Showable {
	virtual void show (string& str) const;
	bool axiom;
	uint label;
	Expr expr;
};

struct Assertion : public Showable {
	Assertion () :
	variables(), disjointed(), essential(),
	floating(), inner(),
	prop(), proof(nullptr), loc() { }
	Assertion (const Location& l) :
	variables(), disjointed(), essential(),
	floating(), inner(),
	prop(), proof(nullptr), loc(l) { }
	virtual ~Assertion() {
		if (proof) delete proof;
	}

	bool areDisjointed (Symbol s1, Symbol s2) const;

	virtual void show(string&) const;

	vector<Variables>  variables;
	vector<Disjointed> disjointed;
	vector<Essential>  essential;
	vector<Floating>   floating;
	vector<Inner>      inner;
	Proposition        prop;
	Proof*             proof;
	Location           loc;
};

class Source : public Showable {
public :
	struct Node {
		Node(Assertion* a) : type (ASSERTION), val() { val.ass = a; }
		Node(Constants* c) : type (CONSTANTS), val() { val.cst = c; }
		Node(Source* s)    : type (SOURCE),    val() { val.src = s; }
		enum Type {
			ASSERTION,
			CONSTANTS,
			SOURCE
		};
		Type type;
		union Value {
			Assertion* ass;
			Constants* cst;
			Source*    src;
		};
		Value val;
	};
	Source(const string& n) :
	top(false), name(n), contents() {
		static bool t = true; top = t; t = false;
	}
	virtual ~Source() {
		for (auto it = contents.begin(); it != contents.end(); ++ it) {
			switch(it->type) {
			case Node::ASSERTION: delete it->val.ass; break;
			case Node::CONSTANTS: delete it->val.cst; break;
			case Node::SOURCE:    delete it->val.src; break;
			default : assert(false && "impossible");
			}
		}
	}

	virtual void show(string&) const;

	bool   top;
	string name;
	vector<Node> contents;
};

ostream& operator << (ostream& os, Symbol symb);
ostream& operator << (ostream& os, const Expr& expr);
ostream& operator << (ostream& os, const Constants* cst);
ostream& operator << (ostream& os, const Ref ref);
ostream& operator << (ostream& os, const Proof* proof);
ostream& operator << (ostream& os, const Variables& vars);
ostream& operator << (ostream& os, const Variables& disj);
ostream& operator << (ostream& os, const Essential& ess);
ostream& operator << (ostream& os, const Floating& flo);
ostream& operator << (ostream& os, const Inner& inn);
ostream& operator << (ostream& os, const Proposition& prop);
ostream& operator << (ostream& os, const Assertion* ass);
ostream& operator << (ostream& os, const Source* src);

}} // mdl::smm


