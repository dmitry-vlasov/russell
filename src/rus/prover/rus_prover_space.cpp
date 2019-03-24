#include "rus_prover_expr.hpp"
#include "rus_prover_space.hpp"
#include "rus_prover_node.hpp"
#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

inline uint find_index(const rus::Assertion* a, const rus::Prop* p) {
	uint c = 0;
	for (auto& x : a->props) if (x.get() == p) return c; else ++c;
	throw Error("prop is not found");
}

Space::Space(rus::Qed* q, Tactic* t) :
	Space(q->step->proof()->thm.get(), q->prop, t) {
}

Space::Space(rus::Assertion* a, rus::Prop* p, Tactic* t) :
	ind(0), root(nullptr), prop(a, find_index(a, p)), tactic_(t) {
	for (auto& p : Sys::mod().math.get<Assertion>()) {
		if (Assertion* ass = p.second.data) {
			if (!ass->token.preceeds(a->token)) {
				continue;
			}
			for (uint i = 0; i < ass->props.size(); ++i) {
				auto& prop = ass->props[i];
				assertions_.add(
					convert_tree(*prop.get()->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX),
					PropRef(ass, i)
				);
			}
		} else {
			throw Error("undefined reference to assertion", Lex::toStr(p.first));
		}
	}
	//if (ind == 18) {
	//cout << "\nASSERTIONS_:\n" << assertions1_.show() << endl;
	//cout << "\nASSERTIONS:\n" << assertions.show() << endl;
	//}
	for (uint i = 0; i < prop.ass->arity(); ++ i) {
		HypRef hypRef(a, i);
		hyps_.add(convert_tree(*hypRef.get()->expr.tree(), ReplMode::DENY_REPL, LightSymbol::MATH_INDEX), hypRef);
	}
	//if (ind == 18) {
		//cout << "\nHYPS:\n" << hyps1_.show() << endl;
	//}
	root = new Hyp(convert_tree(*prop.get()->expr.tree(), ReplMode::DENY_REPL, LightSymbol::MATH_INDEX), this);
	root->buildUp();
}

Return Space::init() {
	string data;
	shown.insert(root->ind);
	data += "<new>\n";
	data += Indent::paragraph(root->show()) + "\n";
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

static void add_shown(set<uint>& shown, set<uint>& to_show, Hyp* hyp);

static void add_shown(set<uint>& shown, set<uint>& to_show, Prop* prop) {
	if (!shown.count(prop->ind)) {
		to_show.insert(prop->ind);
		shown.insert(prop->ind);
		add_shown(shown, to_show, prop->parent);
	}
}

static void add_shown(set<uint>& shown, set<uint>& to_show, Hyp* hyp) {
	if (!shown.count(hyp->ind)) {
		to_show.insert(hyp->ind);
		shown.insert(hyp->ind);
		if (hyp->parent) {
			add_shown(shown, to_show, hyp->parent);
		}
	}
}

void completeDown(set<Node*>& downs) {
	//cout << "COMPLETING: " << ind << endl;
	static  uint c = 0;
	while (!downs.empty()) {
		Node* n = *downs.begin();
		//cout << "DOWNING: " << n->ind << ", c = " << c++ << endl;
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
			completeDown(downs);
			Return ret = check_proved();
			if (ret.success()) {
				return ret;
			} else {
				return Return("leaf node", "</new>");
			}
		} else {
			if (p->mayGrowUp()) {
				p->buildUp();
				set<uint> to_show;
				for (auto& h : p->premises) {
					Hyp* hyp = h.get();
					hyp->buildUp();
					add_shown(shown, to_show, hyp);
				}
				for (auto& h : p->premises) {
					if (Oracle* oracle = dynamic_cast<Oracle*>(tactic_)) {
						if (oracle->hint(p, h.get())) {
							h->unifyWithGoalHyps();
							h->buildDown(downs);
						}
					} else {
						h->unifyWithGoalHyps();
						h->buildDown(downs);
					}
				}
				completeDown(downs);
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

	} else {
		cout << index << " NOT A PROP" << endl;
	}
	return true;
}

Return Space::check_proved() {
	Proved prov = proved();
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
		Return ret = expand(p->ind);
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

Space::Proved Space::proved() {
	Proved ret;
	for (auto& p : root->proofs) {
		if (ProofExp* h = dynamic_cast<ProofExp*>(p.get())) {
			if (rus::Proof* pr = h->proof()) {
				ret.emplace_back(pr);
			} else {
				cout << "h->show(): " << h->show() << endl;
			}
		} else if (ProofTop* h = dynamic_cast<ProofTop*>(p.get())) {
			//if (rus::Proof* pr = make_proof(h->child->step(), prop.ass->id(), prop.get())) {
			//	ret.emplace_back(pr);
			//}
			// TODO
			throw Error("incorrect proved node type");
		} else {
			throw Error("incorrect proved node type");
		}
	}
	return ret;
}

}}}

