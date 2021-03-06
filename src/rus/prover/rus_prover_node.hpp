#pragma once

#include "rus_ast.hpp"
#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

class Space;
class Prop;
class Hyp;
class Ref;
class ProofProp;
class ProofExp;
class ProofNode;
class ProofRef;

struct Node {
	Node(Space* s) : space(s), ind(-1) { }
	Node(Node* n) : space(n->space), ind(-1) { }
	virtual ~Node();

	virtual bool buildDown(set<Node*>&) = 0;
	virtual string show(bool with_proofs = false) const = 0;

	Space* space;
	uint   ind;
	bool   hint = false;
};

inline std::ostream& operator << (std::ostream& os, const Node& n){
	os << n.show(); return os;
}

struct Prop : public Node {
	typedef vector<unique_ptr<Hyp>> Premises;
	typedef vector<unique_ptr<ProofProp>> Proofs;
	Hyp*     parent;
	Premises premises;
	Proofs   proofs;
	PropRef  prop;
	Subst    sub;
	Subst    outer;
	Subst    fresher;
	Prop(PropRef r, Subst&& s, Subst&& o, Subst&& f, Hyp* p);

	bool buildDown(set<Node*>&) override;
	string show(bool with_proofs = false) const override;
	bool mayGrowUp() const { return premises.size() < prop.ass->arity(); }
	bool isLeaf() const { return prop.ass->arity() == 0; }
};

struct Hyp : public Node {
	typedef vector<unique_ptr<Node>> Variants;
	typedef vector<unique_ptr<ProofExp>> Proofs;
	vector<Node*> parents;
	Variants      variants;
	Proofs        proofs;
	Term          expr;
	Hyp(Term&& e, Space* s);
	Hyp(Term&& e, Prop* p);

	bool buildDown(set<Node*>&) override;
	string show(bool with_proofs = false) const override;
	bool root() const { return !parents.size(); }
	Ref* ref();
	bool isLeaf() const { return variants.size() == 0; }
};

struct Ref : public Node {
	typedef vector<unique_ptr<ProofRef>> Proofs;
	Hyp*    parent;
	Hyp*    ancestor;
	VarRepl repl;
	Proofs  proofs;
	Ref(Hyp* p, Hyp* a, Space* s, VarRepl&& r);

	bool buildDown(set<Node*>&) override;
	string show(bool with_proofs = false) const override;
};

string showNodeProofs(const Node* n, uint limit = -1);
string show_nodes_struct(const Node* n);

// Statistics:
void add_sequential_stats(uint card, uint count, Timer& timer);
void add_matrix_stats(uint card, uint count, Timer& timer);
void add_timer_stats(const string& name, Timer& timer);
void print_statistics();

}}}

