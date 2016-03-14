#include <boost/range/adaptor/reversed.hpp>

#include "smm/ast.hpp"
#include "smm/tree.hpp"

namespace mdl { namespace smm {

Tree* to_tree(const Proof* proof) {
	stack<tree::Node> stack;
	Assertion* ass = proof->theorem;
	for (auto r : proof->refs) {
		switch(r.type) {
		case Ref::PREF_E:
		case Ref::PREF_F:
		case Ref::PREF_I:
			stack.push(tree::Node(r, ass)); break;
		case Ref::PREF_A:
		case Ref::PREF_P: {
			Tree* t = new Tree();
			tree::Node a = tree::Node(r);
			t->nodes.push_back(a);
			for (uint i = 0; i < a.val.ass->arity(); ++ i) {
				t->nodes.push_back(stack.top());
				stack.pop();
			}
			std::reverse(t->nodes.begin(), t->nodes.end());
			stack.push(tree::Node(t));
		}	break;
		default : assert(false && "impossible"); break;
		}
	}
	Tree* tree = stack.top().val.tre;
	stack.pop();
	assert(stack.empty());
	return tree;
}

static void to_rpn(const Tree* tree, vector<Ref>& proof) {
	for (auto& node : tree->nodes) {
		if (node.tree)
			to_rpn(node.val.tre, proof);
		else
			proof.push_back(node.ref);
	}
}

Proof* to_rpn(const Tree* tree) {
	Proof* rpn = new Proof();
	vector<Ref>& proof = rpn->refs;
	to_rpn(tree, proof);
	return rpn;
}

void transform(Tree* tree, const tree::Transform& trans, bool forward) {
	for (uint i = 0; i < tree->nodes.size() - 1; ++ i) {
		if (tree->nodes[i].tree)
			transform(tree->nodes[i].val.tre, trans);
	}
	tree::Node op = tree->nodes.back();
	tree::Perm perm = trans.find(op.label())->second;
	assert(perm.size() + 1 == tree->nodes.size());
	vector<tree::Node> new_nodes = tree->nodes;
	for (uint i = 0; i < new_nodes.size() - 1; ++ i)
		if (forward) new_nodes[perm[i]] = tree->nodes[i];
		else         new_nodes[i] = tree->nodes[perm[i]];
	tree->nodes = new_nodes;
}


uint length(const Tree& tree);
uint length(const tree::Node& n) {
	if (n.tree) return length(*n.val.tre);
	else        return 1;
}
uint length(const Tree& tree) {
	uint len = 1;
	for (uint i = 0; i + 1 < tree.nodes.size(); ++ i) {
		len += length(tree.nodes[i]);
	}
	return len;
}

string show(Ref ref) {
	ostringstream os;
	os << ref;
	return os.str();
}

string show(const Tree& tree);

string show(const tree::Node& n) {
	if (n.tree) return show(*n.val.tre);
	else           return show(n.ref);
}

string show(const Tree& tree) {
	const Assertion* ass = tree.nodes.back().val.ass;
	string space = length(tree) > 16 ? "\n" : " ";
	string str = Smm::get().lex.labels.toStr(ass->prop.label);
	str += "(";
	for (uint i = 0; i + 1 <tree.nodes.size(); ++ i)
		str += indent::paragraph(space + show(tree.nodes[i]), "  ");
	str += space + ")";
	return str;
}

ostream& operator << (ostream& os, const Tree& tree) {
	os << show(tree);
	return os;
}

ostream& operator << (ostream& os, const tree::Node& node) {
	if (node.tree) os << *node.val.tre;
	else os << node.ref;
	return os;
}

ostream& operator << (ostream& os, const tree::Perm& perm) {
	for (auto& p : perm) {
		os << p.first << " -> " << p.second << endl;
	}
	return os;
}

}} // mdl::mm


