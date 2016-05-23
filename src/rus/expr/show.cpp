#include "common.hpp"
#include "GLR.hpp"

namespace mdl { namespace rus { namespace expr {

extern LR lr;

string show(const Symbol& s, bool full) {
	if (s == end_marker()) {
		return "<END>";
	} else if (s == eps()) {
		return "<EPS>";
	} else {
		return rus::show(s, full);
	}
}

string show(const Product& p, bool show_left) {
	string str;
	if (show_left)
		str += expr::show(p.left) + " → ";
	for (auto s : p.right)
		str += expr::show(s, true) + " ";
	return str;
}

string show(const Item& it) {
	string str = "item [";
	str += expr::show(it.prod->left) + " → ";
	for (uint i = 0; i < it.prod->right.size(); ++ i) {
		if (i == it.dot) str += " .";
		str += expr::show(it.prod->right[i]) + " ";
	}
	if (it.dot == it.prod->right.size())
		str += ".";
	str += ", " + expr::show(it.lookahead) + "]";
	return str;
}

string show(const State& st) {
	string str = "state ";
	str += to_string(st.ind) + " {\n";
	for (const Item& it : st.items.s) {
		str += "\t" + show(it) + "\n";
	}
	str += "}\n";
	return str;
}

string show(const Action& act) {
	switch (act.kind) {
	case Action::NONE:
		return string("<non>");
	case Action::ACCEPT:
		return string("<acc> ") + to_string(act.val.prod->ind);
	case Action::REDUCE:
		return string("<red> ") + to_string(act.val.prod->ind);
	case Action::SHIFT:
		return string("<shft> ") + to_string(act.val.state->ind);
	default:
		return string("<IMPOSSIBLE> ") + to_string(act.kind);
		//assert(false && "impossible"); return "";
	}
}

string show_symbols() {
	string str;
	str += "Symbols:\n\t";
	for (auto s : lr.symbol_set.s)
		str += expr::show(s) + " ";
	str += "\n";
	str += "Terminals:\n\t";
	for (auto s : lr.terminals.s)
		str += expr::show(s) + " ";
	str += "\n";
	str += "Non-Terminals:\n\t";
	for (auto s : lr.non_terminals.s)
		str += expr::show(s) + " ";
	str += "\n";
	return str;
}

string show_grammar() {
	string str;
	str += "Grammar:\n";
	for (auto s : lr.rule_map.m) {
		str += "\t" + expr::show(s.first) + " ::= \n";
		for (auto p : s.second.s)
			str += "\t\t" + show(*p, false) + "\n";
		str += "\n";
	}
	str += "\n";
	return str;
}

string show(const LR& lr) {
	string str = "LR = \n";

	str += "Symbols:\n\t";
	for (auto s : lr.symbol_set.s)
		str += expr::show(s) + " ";
	str += "\n";
	str += "Terminals:\n\t";
	for (auto s : lr.terminals.s)
		str += expr::show(s) + " ";
	str += "\n";
	str += "Non-Terminals:\n\t";
	for (auto s : lr.non_terminals.s)
		str += expr::show(s) + " ";
	str += "\n";

	str += "Rule map:\n";
	for (auto s : lr.rule_map.m) {
		str += "\t" + expr::show(s.first) + " |--> \n";
		for (auto p : s.second.s)
			str += "\t\t" + show(*p) + "\n";
		str += "\n";
	}
	str += "\n";

	str += "First map:\n";
	for (auto p : lr.first_map.m) {
		str += "\t" + expr::show(p.first) + "\t|--> { ";
		for (auto s : p.second.s)
			str += expr::show(s) + "\t";
		str += "}\n";
	}
	str += "\n";

	str += "Follow map:\n";
	for (auto p : lr.follow_map.m) {
		str += "\t" + expr::show(p.first) + "\t|--> { ";
		for (auto s : p.second.s)
			str += expr::show(s) + "\t";
		str += "}\n";
	}
	str += "\n";

	str += "Products:\n";
	for (auto p : lr.prod_vect)
		str += "\t" + show(*p) + "\n";
	str += "\n";

	str += "Init map:\n";
	for (auto p : lr.init_map.m)
		str += "\t" + show_id(p.first->id) + " |--> " + show(*p.second) + "\n";
	str += "\n";

	str += "States:\n";
	for (State* s : lr.state_set.s)
		str += indent::paragraph(show(*s)) + "\n";
	str += "\n";

	str += "Gotos:\n";
	for (auto p1 : lr.goto_map.m) {
		str += "\t" + to_string(p1.first->ind) + " x\n";
		for (auto p2 : p1.second.m) {
			str += "\t\t" + expr::show(p2.first) + " |--> " + to_string(p2.second->ind) + "\n";
		}
		str += "\n";
	}
	str += "\n";

	return str;
}

string show(const Table& tab) {
	string str = "Tables:\n";
	str += "------------\n";
	str += "Gotos:\n";
	for (auto p1 : tab.gotos.m) {
		str += "\t" + to_string(p1.first->ind) + " x\n";
		for (auto p2 : p1.second.m) {
			str += "\t\t" + expr::show(p2.first) + " |--> " + to_string(p2.second->ind) + "\n";
		}
		str += "\n";
	}
	str += "\n";

	str += "Actions:\n";
	for (auto p1 : tab.actions.m) {
		str += "\t" + to_string(p1.first->ind) + " x\n";
		for (auto p2 : p1.second.m) {
			str += "\t\t" + expr::show(p2.first) + " |--> {";
			//for (auto act : p2.second.s)
			//	str += show(act) + ", ";
			str += "}\n";
		}
		str += "\n";
	}
	str += "\n";

	str += "Inits:\n";
	for (auto p : tab.inits.m) {
		str += "\t" + show_id(p.first->id) +  " |--> " + to_string(p.second->ind) + "\n";
	}
	str += "\n";

	str += "Vars:\n";
	for (auto p : tab.vars.m) {
		str += "\t" + show_id(p.first->id) +  " |--> " + expr::show(p.second) + "\n";
	}
	str += "\n";

	return str;
}



}}} // namespace mdl::rus::expr
