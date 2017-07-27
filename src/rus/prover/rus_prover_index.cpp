#include "rus_prover.hpp"

namespace mdl { namespace rus { namespace prover {

template<class D>
struct IndexImpl : public Index<D> {
	typedef D Data;
	struct Node;
	map<Symbol, Node*> map_;
	void add(const Expr& e, uint i);
	vector<Unified<Data>> unify(const Expr& e) const override;
	~IndexImpl() { for (auto p : map_) delete p.second; }
};

template<class D>
struct IndexImpl<D>::Node {
	typedef D Data;
	IndexImpl<Data>        next;
	vector<User<Data>> data;
};

template<class D>
void IndexImpl<D>::add(const Expr& e, uint id) {
	IndexImpl* i = this;
	Node* n = nullptr;
	for (const auto& s : e) {
		if (!i->map_.count(s)) i->map_[s] = new Node;
		n = i->map_[s];
		i = &n->next;
	}
	n->data.push_back(User<Data>(id));
}

template<class D>
vector<Unified<D>> IndexImpl<D>::unify(const Expr& e) const {
	return vector<Unified<Data>>();
}

static IndexImpl<Assertion> index;

Index<Assertion>& assertion_index() {
	return index;
}

void add_to_index(Assertion* a) {
	for (rus::Prop* p : a->props) {
		index.add(p->expr, a->id());
	}
}

}}}
