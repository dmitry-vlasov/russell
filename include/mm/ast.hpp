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

namespace mdl { namespace mm {

struct Constants {
	Expr expr;
};

struct Ref {
public :
	enum Type {
		PREF_E, ///< "e"
		PREF_F, ///< "f"
		PREF_A, ///< "a"
		PREF_P  ///< "p"
	};
	Type type;
	uint index;
};

class Proof {
public :
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

struct Axiom {
	uint label;
	Expr expr;
};

struct Theorem {
	Theorem() : label(-1), expr(), proof(nullptr) { }
	~Theorem() { if (proof) delete proof; }
	uint   label;
	Expr   expr;
	Proof* proof;
};

class Block;

struct Node {
	Node() : type(NONE), val() { val.non = nullptr;}
	Node(Constants* c)  : type (CONSTANTS),  val() { val.cst = c; }
	Node(Variables* v)  : type (VARIABLES),  val() { val.var = v; }
	Node(Disjointed* d) : type (DISJOINTED), val() { val.dis = d; }
	Node(Floating* f)   : type (FLOATING),   val() { val.flo = f; }
	Node(Essential* e)  : type (ESSENTIAL),  val() { val.ess = e; }
	Node(Axiom* a)      : type (AXIOM),      val() { val.ax  = a; }
	Node(Theorem* t)    : type (THEOREM),    val() { val.th  = t; }
	Node(Block* b)      : type (BLOCK),      val() { val.blk = b; }
	~Node() {
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
		default : assert(false && "impossible"); break;
		}
	}
	void destroy();

	enum Type {
		NONE,
		CONSTANTS,
		VARIABLES,
		DISJOINTED,
		FLOATING,
		ESSENTIAL,
		AXIOM,
		THEOREM,
		BLOCK
	};
	Type type;
	union Value {
		Constants*  cst;
		Variables*  var;
		Disjointed* dis;
		Floating*   flo;
		Essential*  ess;
		Axiom*      ax;
		Theorem*    th;
		Block*      blk;
	};
	Value val;
};

struct Block {
	Block(const string& n) :
	top(false), name(n), contents() {
		static bool t = true; top = t; t = false;
	}
	~ Block() {
		for (auto& node : contents)
			node.destroy();
	}
	bool   top;
	string name;
	vector<Node> contents;
};

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

}} // mdl::mm


