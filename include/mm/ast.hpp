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
	uint label;
	Expr expr;
};

struct Axiom {
	uint label;
	Expr expr;
};

class Proof;

struct Theorem {
	Theorem() : label(-1), expr(), proof(nullptr) { }
	~Theorem();
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
		void*       non;
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

struct Ref {
	Node node;
};

struct Proof {
	vector<Ref> refs;
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


