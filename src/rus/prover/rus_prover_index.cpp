#include "rus_prover.hpp"

namespace mdl { namespace rus { namespace prover {

template<class D>
struct Index {
	typedef D Data;
	struct Node;
	map<Symbol, Node*> map_;
	void add(const Expr& e, uint i);
	~Index() { for (auto p : map_) delete p.second; }
};

template<class D>
struct Index<D>::Node {
	typedef D Data;
	Index<Data>        next;
	vector<User<Data>> data;
};

template<class D>
void Index<D>::add(const Expr& e, uint id) {
	Index* i = this;
	Node* n = nullptr;
	for (const auto& s : e) {
		if (!i->map_.count(s)) i->map_[s] = new Node;
		n = i->map_[s];
		i = &n->next;
	}
	n->data.push_back(User<Data>(id));
}

Index<Assertion>& assertion_index() {
	static Index<Assertion> index;
	return index;
}

void add_to_index(Assertion* a) {
	for (rus::Prop* p : a->props) {
		assertion_index().add(p->expr, a->id());
	}
}

}}}
