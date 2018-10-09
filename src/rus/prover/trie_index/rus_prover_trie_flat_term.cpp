#include "rus_prover_trie_flat_term.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

FlatTerm::FlatTerm(const FlatTerm& t) : nodes(t.nodes) {
	for (uint i = 0; i < nodes.size(); ++ i) {
		auto len = t.nodes[i].end - t.nodes.begin();
		nodes[i].end = nodes.begin() + len;
	}
}

FlatTerm& FlatTerm::operator = (const FlatTerm& t) {
	nodes = t.nodes;
	for (uint i = 0; i < nodes.size(); ++ i) {
		auto len = t.nodes[i].end - t.nodes.begin();
		nodes[i].end = nodes.begin() + len;
	}
	return *this;
}

string FlatTerm::show() const {
	string ret;
	stack<vector<Node>::iterator> st;
	for (auto i = nodes.begin(); i != nodes.end(); ++i) {
		if (i->ruleVar.rule) {
			st.push(i->end);
			ret += i->ruleVar.show() + " (";
		} else {
			ret += i->ruleVar.show() + " ";
		}
		while (!st.empty() && st.top() == i) {
			ret += ") ";
			st.pop();
		}
	}
	return ret;
}

vector<FlatTerm::Iterator> FlatTerm::children(Iterator it) {
	assert(it->ruleVar.isRule());
	vector<Iterator> ret;
	Iterator x = it + 1;
	ret.push_back(x);
	for (uint i = 1; i < it->ruleVar.rule->arity(); ++i) {
		x = x->end + 1;
		ret.push_back(x);
	}
	return ret;
}

vector<FlatTerm::ConstIterator> FlatTerm::children(ConstIterator it) const {
	vector<ConstIterator> ret;
	ConstIterator x = it + 1;
	ret.push_back(x);
	for (uint i = 1; i < it->ruleVar.rule->arity(); ++i) {
		x = x->end + 1;
		ret.push_back(x);
	}
	return ret;
}

FlatTerm::Iterator fill_in_flatterm(auto& ft, const LightTree* t) {
	auto n = ft;
	auto end = ft;
	if (t->kind() == LightTree::VAR) {
		(ft++)->ruleVar.var = t->var();
	} else {
		(ft++)->ruleVar.rule = t->rule();
		for (const auto& c : t->children()) {
			end = fill_in_flatterm(ft, c.get());
		}
	}
	n->end = end;
	return end;
}

FlatTerm convert2flatterm(const LightTree& t) {
	FlatTerm ret(t.len());
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

