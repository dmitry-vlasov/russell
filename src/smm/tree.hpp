#pragma once

#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

struct Tree;

namespace tree {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;

struct Node {
	Node(Ref r)  : ref(r), tree(false), val()  {
		switch (ref.type) {
		case Ref::PREF_A :
		case Ref::PREF_P :
			val.ass = Smm::get().math.assertions[r.index]; break;
		default : assert(false && "impossible"); break;
		}
	}
	Node(Ref r, Assertion* ass)  : ref(r), tree(false), val()  {
		switch (ref.type) {
		case Ref::PREF_E : val.ess = &ass->essential[r.index]; break;
		case Ref::PREF_F : val.flo = &ass->floating[r.index];  break;
		case Ref::PREF_I : val.inn = &ass->inner[r.index];     break;
		default : assert(false && "impossible"); break;
		}
	}
	Node(Tree* t) : ref(), tree(true), val() {
		val.tre = t;
	}
	void destroy();

	uint label() const {
		assert(ref.type == Ref::PREF_A || ref.type == Ref::PREF_P);
		return val.ass->prop.label;
	}

	union Value {
		Floating*   flo;
		Essential*  ess;
		Inner*      inn;
		Assertion*  ass;
		Tree*       tre;
	};
	Ref   ref;
	bool  tree;
	Value val;
};

} // tree

struct Tree {
	~ Tree() {
		for (auto& n : nodes)
			n.destroy();
	}
	vector<tree::Node> nodes;
};

ostream& operator << (ostream& os, const Tree&);
ostream& operator << (ostream& os, const tree::Node&);
ostream& operator << (ostream& os, const tree::Perm&);

inline void tree::Node::destroy() {
	if (tree) delete val.tre;
}

Tree* to_tree(const Proof* pr);
Proof* to_rpn(const Tree* pr);
void transform(Tree* proof, const tree::Transform& trans, bool forward = true);

}} // mdl::smm
