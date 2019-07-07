#include "rus_prover_space.hpp"
#include "rus_prover_node.hpp"
#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

Return Space::init() {
	string data;
	shown.insert(root_->ind);
	data += "<new>\n";
	data += Indent::paragraph(root_->show()) + "\n";
	data += "</new>\n";
	//cout << endl << data << endl;
	return Return("tree created", data);
}

Return Space::info(uint index, string what) {
	if (index >= nodes_.size()) return false;
	string data;
	data += "<info>\n";
	if (what == "node") {
		data += "\t<node>\n";
		data += Indent::paragraph(nodes_[index]->show(), "\t\t") + "\n";
		data += "\t</node>\n";
	} else if (what == "children") {
		if (Prop* p = dynamic_cast<Prop*>(nodes_[index])) {
			data += "\t<children kind=\"prop\">\n";
			for (auto& h : p->premises) {;
				data += Indent::paragraph(h.get()->show(), "\t\t") + "\n";
			}
			data += "\t</children>\n";
		} else if (Hyp* h = dynamic_cast<Hyp*>(nodes_[index])) {
			data += "\t<children kind=\"hyp\">\n";
			for (auto& p : h->variants) {
				data += Indent::paragraph(p.get()->show(), "\t\t") + "\n";
			}
			data += "\t</children>\n";
		}
	} else if (what == "proofs") {
		data += "\t<proofs>\n";
		if (Hyp* h = dynamic_cast<Hyp*>(nodes_[index])) {
			for (auto& p : h->proofs) {
				data += Indent::paragraph(p->show(), "\t\t");
			}
		} else if (Prop* pr = dynamic_cast<Prop*>(nodes_[index])) {
			for (auto& p : pr->proofs) {
				data += Indent::paragraph(p->show(), "\t\t");
			}
		}
		data += "\t</proofs>\n";
	} else if (what == "tree") {
		data += "\t<tree>\n";
		// TODO
		data += "\t</tree>\n";
	} else if (what == "all_nodes") {
		for (const auto& n : nodes_) {
			data += "\t<node>\n";
			data += Indent::paragraph(n.second->show(), "\t\t") + "\n";
			data += "\t</node>\n";
		}
	} else if (what == "all_proofs") {
		for (const auto& n : nodes_) {
			data += Indent::paragraph(showNodeProofs(n.second));
		}
	}
	data += "</info>\n";
	cout << endl << data << endl;
	return Return("node info", data);
}

static void add_shown(set<uint>& shown, set<uint>& to_show, Node* node) {
	if (!shown.count(node->ind)) {
		to_show.insert(node->ind);
		shown.insert(node->ind);
		if (Prop* prop = dynamic_cast<Prop*>(node)) {
			add_shown(shown, to_show, prop->parent);
		} else if (Hyp* hyp = dynamic_cast<Hyp*>(node)) {
			for (Node* parent : hyp->parents) {
				add_shown(shown, to_show, parent);
			}
		} else if (Ref* ref = dynamic_cast<Ref*>(node)) {
			add_shown(shown, to_show, ref->parent);
		} else {
			throw Error("impossibe: no Proof nor Ref nor Hyp");
		}
	}
}

void Space::completeDown(set<Node*>& downs) {
	while (!downs.empty()) {
		Node* n = *downs.begin();
		downs.erase(n);
		n->buildDown(downs);
	}
}

Return Space::expand(uint index) {
	if (index >= nodes_.size()) {
		cout << index << " OUT OF BOUNDARIES" << endl;
		return false;
	}
	if (Prop* p = dynamic_cast<Prop*>(nodes_[index])) {
		set<Node*> downs;
		if (p->isLeaf()) {
			downs.insert(p);
			Timer timer;
			completeDown(downs);
			add_timer_stats("complete_down_leaf", timer);
			Return ret = check_proved();
			if (ret.success()) {
				return ret;
			} else {
				return Return("leaf node", "</new>");
			}
		} else {
			if (p->mayGrowUp()) {
				Timer timer;
				buildUp(p);
				set<uint> to_show;
				for (auto& h : p->premises) {
					Hyp* hyp = h.get();
					buildUp(hyp);
					add_shown(shown, to_show, hyp);
				}
				add_timer_stats("build_up", timer);

				timer.start();
				for (auto& h : p->premises) {
					if (Oracle* oracle = dynamic_cast<Oracle*>(tactic_.get())) {
						initProofs(h.get(), oracle->hint(p, h.get()));
					} else {
						initProofs(h.get());
					}
					if (h->proofs.size()) {
						downs.insert(h.get());
					}
				}
				completeDown(downs);
				add_timer_stats("complete_down", timer);
				Return ret = check_proved();
				if (ret.success()) {
					return ret;
				}
				ostringstream oss;
				oss << "<new>\n";
				for (uint i : to_show) {
					oss << Indent::paragraph(nodes_.at(i)->show()) + "\n";
				}
				oss << "</new>\n";
				//cout << endl << oss.str() << endl;
				return Return("node expanded", oss.str());
			} else {
				return Return("already expanded", "</new>");
			}
		}
	}
	return true;
}

Return Space::check_proved() {
	vector<unique_ptr<rus::Proof>> prov = proved();
	if (prov.size()) {
		ostringstream oss;
		oss << "<proved>\n";
		for (auto& p : prov) {
			oss << "\t<proof>\n";
			oss << "\t<![CDATA[\n";
			oss << Indent::paragraph(p->show(), "\t\t");
			oss << "\t]]>\n";
			oss << "\t</proof>\n";
		}
		oss << "</proved>\n";
		return Return("goal proved", oss.str());
	} else {
		return Return("goal not proved", false);
	}
}

Return Space::prove() {
	while (Prop* p = tactic_->next()) {
		Timer timer;
		Return ret = expand(p->ind);
		add_timer_stats("expand", timer);
		if (ret.msg == "goal proved") {
			return ret;
		}
	}
	return check_proved();
}

Return Space::erase(uint index) {
	if (index >= nodes_.size()) return false;
	delete nodes_[index];
	return true;
}

void delete_steps_recursively(rus::Step* s) {
	for (auto& r : s->refs) {
		if (r.get()->kind() == rus::Ref::STEP) {
			delete_steps_recursively(r.get()->step());
		}
	}
	delete s;
}

vector<unique_ptr<rus::Proof>> Space::proved() {
	vector<unique_ptr<rus::Proof>> ret;
	for (auto& p : root_->proofs) {
		if (ProofHyp* h = dynamic_cast<ProofHyp*>(p.get())) {
			if (auto pr = gen_proof(h)) {
				ret.emplace_back(std::move(pr));
			} /*else {
				cout << "h->show(): " << h->show() << endl;
			}*/
		} else if (ProofTop* h = dynamic_cast<ProofTop*>(p.get())) {
			// TODO
			throw Error("incorrect proved node type");
		} else {
			throw Error("incorrect proved node type");
		}
	}
	return ret;
}

}}}

