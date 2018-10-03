#include "rus_prover_trie_flatterm.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

FlatTerm::FlatTerm(const FlatTerm& t) : nodes(t.nodes) {
	for (uint i = 0; i < nodes.size(); ++ i) {
		auto len = t.nodes[i].end - t.nodes.begin();
		nodes[i].end = nodes.begin() + len;
	}
}

string FlatTerm::show() const {
	string ret;
	stack<Node*> st;
	for (const auto& n : nodes) {
		if (n.ruleVar.rule) {
			st.push(&*n.end);
			ret += n.ruleVar.show() + " (";
		} else {
			ret += n.ruleVar.show() + " ";
		}
		while (st.top() == &n) {
			ret += ")";
		}
	}
	return ret;
}

void fill_in_flatterm(auto& ft, const LightTree* t) {
	auto n = ft;
	if (t->kind() == LightTree::VAR) {
		(ft++)->ruleVar.var = t->var();
	} else {
		auto n = ft;
		(ft++)->ruleVar.rule = t->rule();
		for (const auto& c : t->children()) {
			fill_in_flatterm(ft, c.get());
		}
	}
	n->end = ft;
}

FlatTerm convert2flatterm(const LightTree& t) {
	FlatTerm ret(t.length());
	auto ft = ret.nodes.begin();
	fill_in_flatterm(ft, &t);
	return ret;
}

unique_ptr<LightTree> fill_in_lighttree(auto& ft) {
	if (const Rule* r = (ft++)->ruleVar.rule) {
		LightTree::Children ch;
		for (uint i = 0; i < r->arity(); ++ r) {
			ch.push_back(fill_in_lighttree(ft));
		}
		return make_unique<LightTree>(r, ch);
	} else {
		return make_unique<LightTree>(ft->ruleVar.var);
	}
}

LightTree convert2lighttree(const FlatTerm& ft) {
	auto beg = ft.nodes.begin();
	return LightTree(std::move(*fill_in_lighttree(beg).release()));
}

}}}}

