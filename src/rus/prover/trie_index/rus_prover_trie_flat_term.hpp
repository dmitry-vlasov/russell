#pragma once

#include "../rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct RuleVar {
	const Rule* rule = nullptr;
	LightSymbol var;
	bool operator == (const RuleVar& rv) const { return rule == rv.rule && var == rv.var; }
	bool operator != (const RuleVar& rv) const { return !operator == (rv); }
	bool operator < (const RuleVar& rv) const {
		if (isVar()) {
			return rv.isRule() ? true : var < rv.var;
		} else {
			return rv.isRule() ? rule < rv.rule : false;
		}
	}
	string show() const { return rule ? Lex::toStr(rule->id()) : prover::show(var); }
	bool isVar() const  { return var.is_def(); }
	bool isRule() const { return rule; }
	const Type* type() const { return rule ? rule->type() : var.type; }
};

struct FlatTerm {
	enum Kind { RULE, VAR };
	struct Node {
		Node() { }
		Node(const RuleVar& rv) : ruleVar(rv) { }
		Node(const Node& n) : ruleVar(n.ruleVar) { }
		Node(Node&&) = delete;
		bool operator == (const Node& n) const { return ruleVar == n.ruleVar; }
		bool operator != (const Node& n) const { return ruleVar != n.ruleVar; }
		Node& operator = (const Node& n) { ruleVar = n.ruleVar; return *this;}
		Node& operator = (Node&&) = delete;
		RuleVar ruleVar;
		vector<Node>::iterator end;
	};
	typedef vector<Node>::iterator Iterator;
	typedef vector<Node>::const_iterator ConstIterator;

	struct TermIter {
		TermIter(const FlatTerm& ft) :
			valid_(true), beg_(ft.nodes.begin()), iter_(ft.nodes.begin()), end_(ft.nodes.end()) { }
		TermIter(ConstIterator b, ConstIterator e) :
			valid_(true), beg_(b), iter_(b), end_(e) { }
		TermIter(const TermIter&) = default;
		TermIter& operator = (const TermIter&) = default;
		TermIter side() const { return TermIter(beg_, iter_, end_, false); }
		TermIter next() const {
			if (!valid_ || isNextEnd()) {
				return TermIter(beg_, iter_, end_, false);
			} else {
				return TermIter(beg_, iter_ + 1, end_, iter_ != end_);
			}
		}
		TermIter fastForward() const {
			if (!valid_ || isNextEnd()) {
				return TermIter(beg_, iter_, end_, false);
			} else {
				return TermIter(beg_, iter_->end, end_, iter_ != end_);
			}
		}
		FlatTerm subTerm() const;
		bool isNextEnd() const { return iter_ == end_; }
		bool isSideEnd() const { return true; }
		bool isValid() const { return valid_; }
		ConstIterator iter() const {
			assert(valid_ && "TermIter::iter()");
			return iter_;
		}

	private:
		TermIter(ConstIterator b, ConstIterator i, ConstIterator e, bool v = true) :
			valid_(v), beg_(b), iter_(i), end_(e) { }
		bool valid_;
		ConstIterator beg_;
		ConstIterator iter_;
		ConstIterator end_;
	};

	FlatTerm(uint s) : nodes(s) { }
	FlatTerm(const FlatTerm&);
	FlatTerm(FlatTerm&&) = default;
	FlatTerm(LightSymbol s);
	FlatTerm(const Rule* r, const vector<FlatTerm>& ch);

	bool operator == (const FlatTerm& t) const { return nodes == t.nodes; }
	bool operator != (const FlatTerm& t) const { return nodes != t.nodes; }

	FlatTerm& operator = (const FlatTerm&);
	FlatTerm& operator = (FlatTerm&&) = default;

	Kind kind() const {
		return (nodes.size() == 1 && nodes[0].ruleVar.isVar()) ? VAR : RULE;
	}
	LightSymbol var() const { assert(kind() == VAR); return nodes[0].ruleVar.var; }
	const Rule* rule() const { assert(kind() == RULE); return nodes[0].ruleVar.rule; }
	bool empty() const { return !nodes.size(); }
	uint len() const { return nodes.size(); }
	vector<FlatTerm> children() const;
	vector<ConstIterator> childrenIters() const;
	FlatTerm subTerm(ConstIterator beg) const;

	vector<Node> nodes;
	string show() const;
};

FlatTerm convert2flatterm(const LightTree&);
LightTree convert2lighttree(const FlatTerm&);

}}}}
