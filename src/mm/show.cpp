#include "mm/sys.hpp"
#include "mm/ast.hpp"
#include "mm/tree.hpp"

namespace mdl { namespace mm {

uint length(const Tree& t);
uint length(const Tree::Node& n) {
	return (n.type == Tree::Node::TREE) ? length(*n.val.tree) : 1;
}
uint length(const Tree& t) {
	uint len = 0;
	for (auto n : t.nodes) len += length(n);
	return len;
}
uint length(const Proof& p) {
	return p.refs.size();
}

string show(const Ref& r) {
	return Lex::toStr(r.label());
}
string show(const Tree& tree);
string show(const Tree::Node& n) {
	if (n.type == Tree::Node::TREE)
		return show(*n.val.tree);
	else
		return show(*n.val.ref);
}

string show(const Tree& tree) {
	string space = length(tree) > 16 ? "\n" : " ";
	assert(tree.nodes.back().type == Tree::Node::REF);
	string str = Lex::toStr(tree.nodes.back().val.ref->label());
	str += "(";
	for (uint i = 0; i + 1 <tree.nodes.size(); ++ i)
		str += Indent::paragraph(space + show(tree.nodes[i]), "  ");
	str += space + ") ";
	return str;
}

ostream& operator << (ostream& os, const Constants& cst) {
	os << "$c " << cst.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Ref& ref) {
	os << show_id(ref.label());
	return os;
}

ostream& operator << (ostream& os, const Proof& proof) {
	for (auto r : proof.refs) os << *r << " ";
	os << "$.";
	return os;
}

ostream& operator << (ostream& os, const Variables& vars) {
	os << "$v " << vars.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Disjointed& disj) {
	os << "$d " << disj.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Essential& ess) {
	os << show_id(ess.label) << " $e " << ess.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Floating& flo) {
	os << show_id(flo.label) << " $f " << flo.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Axiom& ax) {
	os << show_id(ax.label) << " $a " << ax.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Theorem& th) {
	os << show_id(th.label) << " $p " << th.expr << "$= ";
	if (th.proof) os << *th.proof;
	return os;
}

ostream& operator << (ostream& os, const Node& node) {
	switch(node.type) {
	case Node::CONSTANTS:  os << *(node.val.cst); break;
	case Node::VARIABLES:  os << *(node.val.var); break;
	case Node::DISJOINTED: os << *(node.val.dis); break;
	case Node::FLOATING:   os << *(node.val.flo); break;
	case Node::ESSENTIAL:  os << *(node.val.ess); break;
	case Node::AXIOM:      os << *(node.val.ax);  break;
	case Node::THEOREM:    os << *(node.val.th);  break;
	case Node::BLOCK:      os << *(node.val.blk); break;
	case Node::COMMENT:    os << *(node.val.com); break;
	case Node::INCLUSION:  os << *(node.val.inc); break;
	default : assert(false && "impossible"); break;
	}
	return os;
}

static int depth(const Block& block) {
	int d = 0;
	Block* b = block.parent;
	while (b) { ++ d; b = b->parent; }
	return d;
}

ostream& operator << (ostream& os, const Block& block) {
	int d = depth(block);
	if (block.parent) os << Indent(d - 1) << "${\n";
	for (auto& node : block.contents)
		os << Indent(d) << node << '\n';
	if (block.parent) os << Indent(d - 1) << "$}";
	return os;
}

ostream& operator << (ostream& os, const Source& source) {
	os << *source.block;
	return os;
}

ostream& operator << (ostream& os, const Inclusion& inc) {
	os << "$[ " << inc.source->name() << ".mm $]";
	return os;
}

ostream& operator << (ostream& os, const Comment& com) {
	os << "$(" << com.text << "$)";
	return os;
}

}} // mdl::mm
