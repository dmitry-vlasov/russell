#include <smm_ast.hpp>

namespace mdl { namespace smm {

ostream& operator << (ostream& os, const Constant& cst) {
	os << "$c " << cst.symb << " $.";
	return os;
}

ostream& operator << (ostream& os, const Ref& ref) {
	switch (ref.type()) {
	case Ref::ESSENTIAL: os << "e"; break;
	case Ref::FLOATING : os << "f"; break;
	case Ref::INNER    : os << "i"; break;
	case Ref::AXIOM    : os << "a"; break;
	case Ref::THEOREM  : os << "p"; break;
	default : assert(false && "impossible"); break;
	}
	if (ref.is_assertion())
		os << show_id(ref.label());
	else
		os << to_string(ref.index());
	return os;
}

ostream& operator << (ostream& os, const Proof& proof) {
	for (Ref* ref : proof.refs) os << *ref << ' ';
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
	os << "e" << to_string(ess.index) << " $e " << ess.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Floating& flo) {
	os << "f" << to_string(flo.index) << " $f " << flo.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Inner& inn) {
	os << "i" << to_string(inn.index) << " $f " << inn.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Proposition& prop) {
	const bool ax = prop.axiom;
	os << (ax ? "a" : "p");
	os << show_id(prop.label);
	os << (ax ? " $a " : " $p ") << prop.expr << (ax ? "$." : "$=");
	return os;
}

template<class T>
void showComponents(ostream& os, const vector<T*>& components) {
	for (auto comp : components)
		os << Indent() << *comp << "\n";
}

ostream& operator << (ostream& os, const Assertion& ass) {
	os << "${\n";
	showComponents<Variables>(os, ass.variables);
	showComponents<Disjointed>(os, ass.disjointed);
	showComponents<Essential>(os, ass.essential);
	showComponents<Floating>(os, ass.floating);
	showComponents<Inner>(os, ass.inner);
	os << Indent() << *ass.prop << "\n";
	if (ass.proof) {
		os << Indent() << *ass.proof << "\n";
	}
	os << "$}";
	return os;
}

ostream& operator << (ostream& os, const Node& node) {
	switch(node.type) {
	case Node::NONE: return os;
	case Node::ASSERTION: os << *(node.val.ass); break;
	case Node::CONSTANT:  os << *(node.val.cst); break;
	case Node::INCLUSION: os << *(node.val.inc); break;
	case Node::COMMENT:   os << *(node.val.com); break;
	default : assert(false && "impossible"); break;
	}
	return os;
}

ostream& operator << (ostream& os, const Source& src) {
	for (auto& node : src.contents) {
		//cout << "writing: " << node << endl;
		os << node << '\n';
	}
	return os;
}

ostream& operator << (ostream& os, const Comment& com) {
	os << "$(" << com.text << "$)";
	return os;
}

ostream& operator << (ostream& os, const Inclusion& inc) {
	os << "$[ " << inc.source.get()->name() << ".smm $]";
	return os;
}

}} // mdl::smm
