#pragma once

#include "std.hpp"
#include "error.hpp"

namespace mdl {

template<class Label>
struct DAG {
	struct Node {
		Node(Label l, uint a) : label_(l), children_(a) { }
		Node(const Node& d) : label_(d.label_), children_(d.childrenArity()) {
			for (uint i = 0; i < d.childrenArity(); ++ i) {
				if (d.getChild(i)) {
					setChild(i, new Node(*d.getChild(i)));
				}
			}
		}
		Label label() const { return label_; }
		bool isLeaf() const { return childrenArity() == 0; }
		bool isRoot() const { return parentsArity() == 0; }
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
		string show(std::function<string (const Label&)> f) const {
			string ret;
			ret += f(label_) + "(";
			if (children_.size()) {
				if (children_[0]) {
					ret += children_[0]->show(f);
				} else {
					ret += "*";
				}
				for (uint i = 1; i < children_.size(); ++ i) {
					if (children_[i]) {
						ret += ", " + children_[i]->show(f);
					} else {
						ret += ", *";
					}
				}
			}
			ret += ")";
			return ret;
		}
		bool operator == (const Node& n) const {
			if (label_ != n.label_ || children_.size() != n.children_.size()) {
				return false;
			} else {
				for (uint i = 0; i < children_.size(); ++i) {
					if (bool(children_.at(i)) != bool(n.children_.at(i))) {
						return false;
					}
					if (children_.at(i) && *children_.at(i) != *n.children_.at(i)) {
						return false;
					}
				}
				return true;
			}
		}
		bool operator != (const Node& n) const {
			return !operator ==(n);
		}
		bool operator < (const Node& n) const {
			     if (label_ < n.label_) return true;
			else if (n.label_ < label_) return false;
			else if (children_.size() < n.children_.size()) return true;
			else if (n.children_.size() < children_.size()) return false;
			else {
				for (uint i = 0; i < children_.size(); ++i) {
					auto& a = children_.at(i);
					auto& b = n.children_.at(i);
					     if (bool(a) < bool(b)) return true;
					else if (bool(b) < bool(a)) return false;
					else if (a) {
						     if (*a < *b) return true;
						else if (*b < *a) return false;
					}
				}
				return false;
			}
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
	DAG(DAG&& d) : roots_(std::move(d.roots_)), leafs_(std::move(d.leafs_)), size_(d.size_) { }
	DAG& operator = (DAG&& d) {
		roots_ = std::move(d.roots_);
		leafs_ = std::move(d.leafs_);
		size_ = d.size_;
		return *this;
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
	bool operator == (const DAG& d) const {
		     if (size_ != d.size_) return false;
		else if (roots_.size() != d.roots_.size()) return false;
		else {
			for (uint i = 0; i < roots_.size(); ++ i){
				if (*roots_.at(i) != *d.roots_.at(i)) {
					return false;
				}
			}
			return true;
		}
	}
	bool operator != (const DAG& d) const {
		return !operator==(d);
	}
	bool operator < (const DAG& d) const {
		     if (size_ < d.size_) return true;
		else if (d.size_ < size_) return false;
		else if (roots_.size() < d.roots_.size()) return true;
		else if (d.roots_.size() < roots_.size()) return false;
		else {
			for (uint i = 0; i < roots_.size(); ++i) {
				     if (*roots_.at(i) < *d.roots_.at(i)) return true;
				else if (*d.roots_.at(i) < *roots_.at(i)) return false;
			}
			return false;
		}
	}

private:
	vector<unique_ptr<Node>> roots_;
	vector<Leaf> leafs_;
	uint size_;
};

}
