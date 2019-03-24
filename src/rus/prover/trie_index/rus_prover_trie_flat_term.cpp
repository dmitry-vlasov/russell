#include "rus_prover_trie_flat_term.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_flatterm = false;

void copyFlatSubTerm(FlatTerm* t, const uint pos, FlatTerm::ConstIterator b) {
	uint i = 0;
	uint wd = 0;

	static int c = 0;
	++c;
	bool debug = t->nodes.size() == 0; //(c == 1);
	if (debug_flatterm) {
		cout << "t->nodes.size() = " << t->nodes.size() << endl;
		cout << "b: " << b->ruleVar.show() << endl;
		cout << "b->end: " << b->end->ruleVar.show() << endl;
		cout << "b->end - b: " << (int)(b->end - b) << endl;
		cout << "pos: " << pos << endl;
	}

	for (auto it = b; ; ++ it) {
		//if (debug) {
		//	cout << "it->ruleVar: " << it->ruleVar.show()  << endl;
		//}

		t->nodes[pos + i].ruleVar = it->ruleVar;
		t->nodes[pos + i].end = t->nodes.begin() + pos + (it->end - b);
		if (it == b->end) {
			break;
		}
		++i;
		++wd;
		if (wd > 1024) {
			cout << "SOMETH WRONG: " << c << ", wd: " << wd << endl;
			break;
		}
	}
	if (debug_flatterm) {
		cout << "COPIED: " << t->show() << endl;
		t->verify();
	}
}

FlatTerm FlatTerm::TermIter::subTerm() const {
	FlatTerm ret((iter_->end - iter_) + 1);
	if (ret.nodes.size()) {
		copyFlatSubTerm(&ret, 0, iter_);
	}
	return ret;
}

FlatTerm FlatTerm::TermIter::term() const {
	FlatTerm ret((end_ - beg_) + 1);
	if (ret.nodes.size()) {
		copyFlatSubTerm(&ret, 0, beg_);
	}
	return ret;
}


FlatTerm::FlatTerm(const FlatTerm& t) : nodes(t.nodes.size()) {
	if (t.nodes.size()) {
		copyFlatSubTerm(this, 0, t.nodes.begin());
	}
}

FlatTerm::FlatTerm(ConstIterator i) : nodes(i->end - i) {
	if (nodes.size()) {
		copyFlatSubTerm(this, 0, i);
	}
}

FlatTerm::FlatTerm(LightSymbol s) : nodes(1) {
	nodes[0].ruleVar.var = s;
	nodes[0].end = nodes.begin();
	if (debug_flatterm) {
		verify();
	}
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
		copyFlatSubTerm(this, pos, c.nodes.begin());
		pos += c.len();
	}
	if (debug_flatterm) {
		verify();
	}
}

FlatTerm& FlatTerm::operator = (const FlatTerm& t) {
	nodes = vector<Node>(t.nodes.size());
	if (t.nodes.size()) {
		copyFlatSubTerm(this, 0, t.nodes.begin());
	}
	return *this;
}

string showFlatTerm(FlatTerm::ConstIterator i) {
	if (i->ruleVar.isRule()) {
		string ret;
		auto it = i + 1;
		for (const auto& s : i->ruleVar.rule->term) {
			if (s.kind() == Symbol::CONST) {
				ret += show(s) + " ";
			} else {
				ret += showFlatTerm(it) + " ";
				it = it->end + 1;
			}
		}
		return ret;
	} else {
		return show(i->ruleVar.var);
	}
}

string FlatTerm::show(bool simple) const {
	if (simple) {
		string ret;
		for (auto i = nodes.cbegin(); i != nodes.cend(); ++i) {
			ret += i->ruleVar.show() + " ";
		}
		return ret;
	} else {
		if (!nodes.size()) {
			return "<empty>";
		} else {
			return showFlatTerm(nodes.begin());
		}
	}
}
/*
string FlatTerm::show(bool simple) const {
	string ret;
	stack<vector<Node>::const_iterator> st;
	for (auto i = nodes.cbegin(); i != nodes.cend(); ++i) {
		if (simple) {
			ret += i->ruleVar.show() + " ";
		} else {
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
	}
	return ret;
}*/

string FlatTerm::show_pointers() const {
	ostringstream oss;
	for (auto i = nodes.cbegin(); i != nodes.cend(); ++i) {
		oss << i->ruleVar.show() << "=(" << (void*)&*i << " ";
	}
	oss << endl;
	return oss.str();
}

vector<FlatTerm> FlatTerm::children() const {
	vector<FlatTerm> ret;
	if (kind() == RULE) {
		ConstIterator x = nodes.begin() + 1;
		for (uint i = 1; i < nodes[0].ruleVar.rule->arity(); ++i) {
			FlatTerm t = subTerm(x);
			ret.push_back(t);
			x = x->end + 1;
		}
	}
	return ret;
}

vector<FlatTerm::ConstIterator> FlatTerm::childrenIters() const {
	vector<FlatTerm::ConstIterator> ret;
	//cout << "CHILDREN OF: " << show() << endl;
	if (kind() == RULE && nodes.size()) {
		ConstIterator x = nodes.begin() + 1;
		for (uint i = 0; i < nodes[0].ruleVar.rule->arity(); ++i) {
			ret.push_back(x);
			/*cout << "\tCHILD: '";
			auto it = x;
			while (true) {
				cout << it->ruleVar.show() << " ";
				if (it == x->end) {
					break;
				}
				++it;
			}
			cout << "'" << endl;*/
			x = x->end + 1;
		}
	}
	//cout << "END CHILDREN" << endl;
	return ret;
}

FlatTerm term(FlatTerm::ConstIterator beg) {
	FlatTerm ret((beg->end - beg) + 1);
	copyFlatSubTerm(&ret, 0, beg);
	return ret;
}

FlatTerm FlatTerm::subTerm(ConstIterator beg) const {
	FlatTerm ret((beg->end - beg) + 1);
	copyFlatSubTerm(&ret, 0, beg);
	return ret;
}

void FlatTerm::verify() const {
	if (nodes.begin()->ruleVar.isRule()) {
		stack<vector<Node>::const_iterator> st;
		for (auto i = nodes.begin(); i != nodes.end(); ++i) {
			if (i->ruleVar.isRule()) {
				st.push(i->end);
			}
			while (!st.empty() && i == st.top()) {
				st.pop();
			}
		}
		if (!st.empty()) {
			//cout << "st.top()->show() = " << st.top()->ruleVar.show() << endl;
			throw Error("broken term: non-empty stack", show(true) + "\n" + show(false));
		}
	} else if (!nodes.begin()->ruleVar.isVar()) {
		throw Error("broken term: non var neither rule", show(true) + "\n" + show(false));
	}
}

FlatTerm::Iterator fill_in_flatterm(FlatTerm::Iterator& ft, const LightTree* t) {
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

unique_ptr<LightTree> fill_in_lighttree(FlatTerm::ConstIterator& ft, FlatTerm::ConstIterator end) {
	if (ft->ruleVar.isRule()) {
		const Rule* r = (ft++)->ruleVar.rule;
		LightTree::Children ch;
		for (uint i = 0; i < r->arity(); ++ i) {
			ch.push_back(fill_in_lighttree(ft, end));
		}
		return make_unique<LightTree>(r, ch);
	} else {
		return make_unique<LightTree>((ft++)->ruleVar.var);
	}
}

LightTree convert2lighttree(const FlatTerm& ft) {
	auto beg = ft.nodes.begin();
	return LightTree(std::move(*fill_in_lighttree(beg, ft.nodes.end()).get()));
}

}}}}
