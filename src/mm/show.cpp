#include "mm/ast.hpp"
#include "mm/globals.hpp"
#include "mm/tree.hpp"

namespace mdl { namespace mm {

uint length(const Proof& p);
uint length(const Node& n) {
	if (n.type == Node::PROOF) return length(*n.val.prf);
	else return 1;
}
uint length(const Proof& p) {
	assert(p.tree);
	uint len = 1;
	for (uint i = 0; i + 1 < p.refs.size(); ++ i) {
		len += length(p.refs[i]);
	}
	return len;
}

string show(const Proof& tree);
string show(const Node& n) {
	if (n.type == Node::PROOF)
		return show(*n.val.prf);
	else {
		uint lab = -1;
		switch(n.type) {
		case Node::FLOATING:   lab = n.val.flo->label; break;
		case Node::ESSENTIAL:  lab = n.val.ess->label; break;
		default : assert(false && "impossible"); break;
		}
		return Mm::get().lex.labels.toStr(lab);
	}
}

string show(const Proof& tree) {
	string space = length(tree) > 16 ? "\n" : " ";
	string str = Mm::get().lex.labels.toStr(node_label(tree.refs.back()));
	str += "(";
	for (uint i = 0; i + 1 <tree.refs.size(); ++ i)
		str += indent::paragraph(space + show(tree.refs[i]), "  ");
	str += space + ")";
	return str;
}


ostream& operator << (ostream& os, const Constants& cst) {
	os << "$c " << cst.expr << "$.";
	return os;
}

class ref {
	Node node;
public:
	ref(Node n) : node(n) {
	}
	void write(ostream& os) {
		switch (node.type) {
		case Node::FLOATING:   os << label(node.val.flo->label); break;
		case Node::ESSENTIAL:  os << label(node.val.ess->label); break;
		case Node::AXIOM:      os << label(node.val.ax->label);  break;
		case Node::THEOREM:    os << label(node.val.th->label);  break;
		case Node::PROOF:      os << *node.val.prf;           break;
		default :              assert(false && "impossible"); break;
		}
	}
};

ostream& operator << (ostream& os, ref r) {
	r.write(os);
	return os;
}

ostream& operator << (ostream& os, const Proof& proof) {
	if (proof.tree) {
		os << show(proof);
		return os;
	}
	for (auto& node : proof.refs)
		os << ref(node) << ' ';
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
	os << label(ess.label) << " $e " << ess.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Floating& flo) {
	os << label(flo.label) << " $f " << flo.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Axiom& ax) {
	os << label(ax.label) << " $a " << ax.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Theorem& th) {
	os << label(th.label) << " $p " << th.expr << "$= " << *th.proof;
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
	if (!block.name.empty() && block.parent)
		os << indent(d - 1) << "$[" << block.name << "$]";
	else {
		if (block.parent) os << indent(d - 1) << "${\n";
		for (auto& node : block.contents)
			os << indent(d) << node << '\n';
		if (block.parent) os << indent(d - 1) << "$}";
		else os << "\n";
	}
	return os;
}

}} // mdl::mm
