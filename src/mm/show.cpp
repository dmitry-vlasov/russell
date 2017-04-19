#include "mm/sys.hpp"
#include "mm/ast.hpp"

namespace mdl { namespace mm {

ostream& operator << (ostream& os, const Constant& cst) {
	os << "$c " << cst.symb << " $.";
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
	os << show_id(ess.id()) << " $e " << ess.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Floating& flo) {
	os << show_id(flo.id()) << " $f " << flo.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Axiom& ax) {
	os << show_id(ax.id()) << " $a " << ax.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Theorem& th) {
	os << show_id(th.id()) << " $p " << th.expr << "$= ";
	if (th.proof) os << *th.proof;
	return os;
}

ostream& operator << (ostream& os, const Node& node) {
	switch(node.type) {
	case Node::CONSTANT:   os << *(node.val.cst); break;
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
