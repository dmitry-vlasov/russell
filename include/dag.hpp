#pragma once
#include "std.hpp"

namespace mdl {

template<class Label>
struct DAG {
	struct Node {
		Node(Label l, uint a) : label_(l), children_(a) { }
		Node(const Node& d) : label_(d.label_), children_(d.childrenArity()) {
			for (uint i = 0; i < d.childrenArity(); ++ i) {
				setChild(i, new Node(*d.getChild(i)));
			}
		}
		Label label() const { return label_; }
		uint parentsArity() const { return parents_.size(); }
		uint childrenArity() const { return children_.size(); }
		const Node* getParent(uint i) const { return parents_.at(i); }
		const Node* getChild(uint i) const { return children_.at(i).get(); }
		void setChild(uint i, Node* ch) {
			children_[i].reset(ch);
			ch->parents_.push_back(this);
		}
		void traverse(std::function<void (Node&)> f) {
			f(*this); for (auto& c : children_) if (c) c->traverse(f);
		}
		void traverse(std::function<void (const Node&)> f) const {
			f(*this); for (const auto& c : children_) if (c) c->traverse(f);
		}
	private:
		Label label_;
		vector<unique_ptr<Node>> children_;
		vector<const Node*> parents_;
	};
	struct Leaf {
		Leaf(Node* n, uint i) : node(n), ind(i) { }
		bool operator < (const Leaf& l) const {
			if (node < l.node) return true;
			else if (node > l.node) return false;
			else return ind < l.ind;
		}
		bool operator ==(const Leaf& l) const {
			return node == l.node && ind == l.ind;
		}
		bool operator !=(const Leaf& l) const {
			return !operator ==(l);
		}
		Node* node;
		uint  ind;
	};

	DAG(Label l, uint a) : size_(1) {
		roots_.emplace_back(new Node(l, a));
		for (uint i = 0; i < a; ++ i) {
			leafs_.emplace_back(roots_[0].get(), i);
		}
	}
	DAG(const DAG& d) : size_(d.size_) {
		for (uint i = 0; i < d.rootSize(); ++ i) {
			roots_.emplace_back(new Node(*d.getRoot(i)));
			roots_.back()->traverse(
				[this](Node& n) {
					for (uint i = 0; i < n.childrenArity(); ++ i) {
						if (!n.getChild(i)) {
							leafs_.emplace_back(&n, i);
						}
					}
				}
			);
		}
	}
	uint rootSize() const { return roots_.size(); }
	uint leafSize() const { return leafs_.size(); }
	const Node* getRoot(uint i) const { return roots_.at(i).get(); }
	const Leaf& getLeaf(uint i) const { return leafs_.at(i); }
	void expandLeaf(Leaf leaf, Node* new_leaf) {
		auto li = std::find(leafs_.begin(), leafs_.end(), leaf);
		if (li != leafs_.end()) {
			leafs_.erase(li);
			leaf.node->setChild(leaf.ind, new_leaf);
			for (uint i = 0; i < new_leaf->childrenArity(); ++i) {
				leafs_.emplace_back(new_leaf, i);
			}
			++ size_;
		} else {
			throw Error("no such leaf in DAG");
		}
	}
	void expandLeaf(uint leaf_ind, Node* new_leaf) {
		expandLeaf(leafs_[leaf_ind], new_leaf);
	}
	void expandLeaf(uint leaf_ind, Label l, uint a) {
		expandLeaf(leafs_[leaf_ind], new Node(l, a));
	}
	uint size() const { return size_; }

private:
	vector<unique_ptr<Node>> roots_;
	vector<Leaf> leafs_;
	uint size_;
};

}
