#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

void Constants::show (string& str) const {
	//str += gen::constants(this);
	str += "$c ";
	expr.show(str);
	str += "$.";
};


void Ref::show (string& str) const {
	switch (type) {
	case PREF_E: str += "e"; break;
	case PREF_F: str += "f"; break;
	case PREF_I: str += "i"; break;
	case PREF_A: str += "a"; break;
	case PREF_P: str += "p"; break;
	}
	if (Smm::get().config.labels && (type == PREF_A || type == PREF_P))
		str += Smm::get().lex.labels.toStr(index);
	else
		str += std::to_string(index);
}


void Proof::show (string& str) const {
	for (auto it = refs.cbegin(); it != refs.cend(); ++ it) {
		it->show(str);
		str += ' ';
	}
	str += "$.";
}


void Variables::show (string& str) const {
	str += "$v ";
	expr.show(str);
	str += "$.";
}

void Disjointed::show (string& str) const {
	str += "$d ";
	expr.show(str);
	str += "$.";
}

void Essential::show (string& str) const {
	str += "e";
	str += std::to_string(index);
	str += " $e ";
	expr.show(str);
	str += "$.";
}

void Floating::show (string& str) const {
	str += "f";
	str += std::to_string(index);
	str += " $f ";
	expr.show(str);
	str += "$.";
}

void Inner::show (string& str) const {
	str += "i";
	str += std::to_string(index);
	str += " $i ";
	expr.show(str);
	str += "$.";
}

void Proposition::show (string& str) const {
	str += axiom ? "a" : "p";
	if (Smm::get().config.labels)
		str += Smm::get().lex.labels.toStr(label);
	else
		str += std::to_string(label);
	str += axiom ? " $a " : " $p ";
	expr.show(str);
	str += axiom ? "$." : "$=";
}


bool Assertion::areDisjointed (Symbol s1, Symbol s2) const {
	for (auto it = disjointed.cbegin(); it != disjointed.cend(); ++ it) {
		if (it->expr.contains(s1) && it->expr.contains(s2))
			return true;
	}
	return false;
}


template<class T>
void showComponents(string& str, const T& components) {
	for (auto it = components.cbegin(); it != components.cend(); ++ it) {
		str += "\t"; it->show(str); str += "\n";
	}
}

void Assertion::show (string& str) const {
	str += "${\n";
	showComponents(str, variables);
	showComponents(str, disjointed);
	showComponents(str, essential);
	showComponents(str, floating);
	showComponents(str, inner);
	str += "\t"; prop.show(str); str += "\n";
	if (proof) {
		str += "\t"; proof->show(str); str += "\n";
	}
	str += "$}\n";
}

void Source::show(string& str) const {
	//str += gen::source(this);
	if (top) {
		for (auto it = contents.cbegin(); it != contents.cend(); ++ it) {
			switch(it->type) {
			case Node::ASSERTION: it->val.ass->show(str); break;
			case Node::CONSTANTS: it->val.cst->show(str); break;
			case Node::SOURCE:    it->val.src->show(str);    break;
			default : assert(false && "impossible");
			}
			str += '\n';
		}
	} else {
		str += "$[";
		str += name;
		str += "$]";
	}
}

}} // mdl::smm
