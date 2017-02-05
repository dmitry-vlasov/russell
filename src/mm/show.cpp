#include "mm/ast.hpp"
#include "mm/globals.hpp"
#include "mm/tree.hpp"

namespace mdl { namespace mm {

uint length(const Proof& p);
uint length(const Ref& r) {
	if (r.type == Ref::PROOF) return length(*r.val.prf);
	else return 1;
}
uint length(const Proof& p) {
	assert(p.type == Proof::TREE);
	uint len = 1;
	for (uint i = 0; i + 1 < p.refs.size(); ++ i) {
		len += length(p.refs[i]);
	}
	return len;
}

string show(const Proof& tree);
string show(const Ref& r) {
	if (r.type == Ref::PROOF)
		return show(*r.val.prf);
	else
		return System::get().lex.labels.toStr(r.label());
}

string show(const Proof& tree) {
	string space = length(tree) > 16 ? "\n" : " ";
	string str = System::get().lex.labels.toStr(tree.refs.back().label());
	str += "(";
	for (uint i = 0; i + 1 <tree.refs.size(); ++ i)
		str += indent::paragraph(space + show(tree.refs[i]), "  ");
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


void write_proof_ref(ostream& os, const Ref& r) {
	if (r.type == Ref::PROOF)
		os << *r.val.prf << ' ';
	else
		os << r << ' ';
}

ostream& operator << (ostream& os, const Proof& proof) {
	if (proof.type == Proof::TREE) {
		os << show(proof);
		return os;
	}
	for (auto& node : proof.refs)
		write_proof_ref(os, node);
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
	if (block.parent) os << indent(d - 1) << "${\n";
	for (auto& node : block.contents)
		os << indent(d) << node << '\n';
	if (block.parent) os << indent(d - 1) << "$}";
	return os;
}

ostream& operator << (ostream& os, const Source& source) {
	os << *source.block;
	return os;
}

ostream& operator << (ostream& os, const Inclusion& inc) {
	os << "$[ " << inc.source->name << ".mm $]";
	return os;
}

ostream& operator << (ostream& os, const Comment& com) {
	os << "$(" << com.text << "$)";
	return os;
}

}} // mdl::mm
