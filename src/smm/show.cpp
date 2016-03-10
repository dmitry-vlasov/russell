#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

ostream& operator << (ostream& os, const Constants& cst) {
	os << "$c " << cst.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Ref& ref) {
	switch (ref.type) {
	case Ref::PREF_E: os << "e"; break;
	case Ref::PREF_F: os << "f"; break;
	case Ref::PREF_I: os << "i"; break;
	case Ref::PREF_A: os << "a"; break;
	case Ref::PREF_P: os << "p"; break;
	}
	if (Smm::get().config.labels && (ref.type == Ref::PREF_A || ref.type == Ref::PREF_P))
		os << Smm::get().lex.labels.toStr(ref.index);
	else
		os << to_string(ref.index);
	return os;
}

ostream& operator << (ostream& os, const Proof& proof) {
	for (auto it = proof.refs.cbegin(); it != proof.refs.cend(); ++ it)
		os << *it << ' ';
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
	os << "i" << to_string(inn.index) << " $i " << inn.expr << "$.";
	return os;
}

ostream& operator << (ostream& os, const Proposition& prop) {
	const bool ax = prop.axiom;
	os << (ax ? "a" : "p");
	if (Smm::get().config.labels)
		os << Smm::get().lex.labels.toStr(prop.label);
	else
		os << to_string(prop.label);
	os << (ax ? " $a " : " $p ") << prop.expr << (ax ? "$." : "$=");
	return os;
}

template<class T>
void showComponents(ostream& os, const vector<T>& components) {
	for (auto it = components.cbegin(); it != components.cend(); ++ it)
		os << "\t" << *it << "\n";
}

ostream& operator << (ostream& os, const Assertion& ass) {
	os << "${\n";
	showComponents<Variables>(os, ass.variables);
	showComponents<Disjointed>(os, ass.disjointed);
	showComponents<Essential>(os, ass.essential);
	showComponents<Floating>(os, ass.floating);
	showComponents<Inner>(os, ass.inner);
	os << "\t" << ass.prop << "\n";
	if (ass.proof) {
		os << "\t" << ass.proof << "\n";
	}
	os << "$}\n";
	return os;
}

ostream& operator << (ostream& os, const Source& src) {
	if (src.top) {
		for (auto it = src.contents.cbegin(); it != src.contents.cend(); ++ it) {
			switch(it->type) {
			case Source::Node::ASSERTION: os << *(it->val.ass); break;
			case Source::Node::CONSTANTS: os << *(it->val.cst); break;
			case Source::Node::SOURCE:    os << *(it->val.src); break;
			default : assert(false && "impossible");
			}
			os << '\n';
		}
	} else
		os << "$[" << src.name << "$]";
	return os;
}

}} // mdl::smm
