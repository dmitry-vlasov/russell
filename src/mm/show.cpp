#include "mm/ast.hpp"
#include "mm/globals.hpp"

namespace mdl { namespace mm {

ostream& operator << (ostream& os, const Constants& cst) {
	os << "$c " << cst.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Ref& ref) {
	switch (ref.node.type) {
	case Node::NONE:       assert(false && "impossible"); break;
	case Node::CONSTANTS:  assert(false && "impossible"); break;
	case Node::VARIABLES:  assert(false && "impossible"); break;
	case Node::DISJOINTED: assert(false && "impossible"); break;
	case Node::FLOATING:   os << Mm::get().lex.labels.toStr(ref.node.val.flo->label); break;
	case Node::ESSENTIAL:  os << Mm::get().lex.labels.toStr(ref.node.val.ess->label); break;
	case Node::AXIOM:      os << Mm::get().lex.labels.toStr(ref.node.val.ax->label);  break;
	case Node::THEOREM:    os << Mm::get().lex.labels.toStr(ref.node.val.th->label);  break;
	case Node::BLOCK:      assert(false && "impossible"); break;
	default :              assert(false && "impossible"); break;
	}
	return os;
}

ostream& operator << (ostream& os, const Proof& proof) {
	for (auto& ref : proof.refs)
		os << ref << ' ';
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
	os << Mm::get().lex.labels.toStr(ess.label) << " $e " << ess.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Floating& flo) {
	os << Mm::get().lex.labels.toStr(flo.label) << " $f " << flo.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Axiom& ax) {
	os << Mm::get().lex.labels.toStr(ax.label) << " $a " << ax.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Theorem& th) {
	os << Mm::get().lex.labels.toStr(th.label) << " $p " << th.expr << "$= " << *th.proof;
	return os;
}

ostream& operator << (ostream& os, const Node& node) {
	switch(node.type) {
	case Node::NONE: return os;
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

ostream& operator << (ostream& os, const Block& block) {
	//if (block.top) {
		os << "${\n";
		for (auto& node : block.contents)
			os << '\t' << node << '\n';
		os << "$}\n";
	//} else
	//	os << "${" << block.name << "$}";
	return os;
}

}} // mdl::mm
