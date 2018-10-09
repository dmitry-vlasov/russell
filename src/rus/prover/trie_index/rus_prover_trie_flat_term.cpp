#include "rus_prover_trie_flat_term.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

void copyFlatSubTerm(FlatTerm* t, const uint pos, const FlatTerm& s, FlatTerm::ConstIterator b) {
	uint i = 0;
	for (auto it = b; ; ++ i) {
		t->nodes[pos + i].ruleVar = it->ruleVar;
		t->nodes[pos + i].end = t->nodes.begin() + pos + (it->end - b);
		if (it == b->end) {
			break;
		}
		++i;
	}
}

FlatTerm::FlatTerm(const FlatTerm& t) : nodes(t.nodes.size()) {
	copyFlatSubTerm(this, 0, t, t.nodes.begin());
}

FlatTerm::FlatTerm(LightSymbol s) : nodes(1) {
	nodes[0].ruleVar.var = s;
	nodes[0].end = nodes.begin();
}

static uint flatTermsLen(const vector<FlatTerm>& ch) {
	uint len = 1;
	for (const auto& c : ch) {
		len += c.len();
	}
	return len;
}

FlatTerm::FlatTerm(const Rule* r, const vector<FlatTerm>& ch) : nodes(flatTermsLen(ch)) {
	nodes[0].ruleVar.rule = r;
	nodes[0].end = nodes.begin() + nodes.size() - 1;
	uint pos = 1;
	for (const auto& c : ch) {
		copyFlatSubTerm(this, pos, c, c.nodes.begin());
		pos += c.len();
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

vector<FlatTerm> FlatTerm::children() const {
	vector<FlatTerm> ret;
	if (kind() == RULE) {
		ConstIterator x = nodes.begin() + 1;
		for (uint i = 1; i < nodes[0].ruleVar.rule->arity(); ++i) {
			ret.push_back(subTerm(x));
			x = x->end + 1;
		}
	}
	return ret;
}

vector<FlatTerm::ConstIterator> FlatTerm::childrenIters() const {
	vector<FlatTerm::ConstIterator> ret;
	if (kind() == RULE) {
		ConstIterator x = nodes.begin() + 1;
		for (uint i = 1; i < nodes[0].ruleVar.rule->arity(); ++i) {
			ret.push_back(x);
			x = x->end + 1;
		}
	}
	return ret;
}

FlatTerm FlatTerm::subTerm(ConstIterator beg) const {
	FlatTerm ret(beg->end - beg);
	copyFlatSubTerm(&ret, 0, *this, beg);
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

