#include "rus_prover_expr.hpp"
#include "rus_prover_space.hpp"
#include "rus_prover_node.hpp"

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
	root(nullptr), prop(a, find_index(a, p)), tactic_(t) {
	for (auto& p : Sys::mod().math.get<Assertion>()) {
		if (Assertion* ass = p.second.data) {
			if (!ass->token.preceeds(a->token)) {
				continue;
			}
			uint c = 0;
			for (auto& prop : ass->props) {
				assertions.add(
					convert_tree(*prop.get()->expr.tree()),
					PropRef(ass, c++)
				);
			}
		} else {
			throw Error("undefined reference to assertion", Lex::toStr(p.first));
		}
	}
	cout << "\nASSERTIONS:\n" << assertions.show() << endl;
	for (uint i = 0; i < prop.ass->arity(); ++ i) {
		HypRef hypRef(a, i);
		hyps.add(convert_tree(*hypRef.get()->expr.tree(), ReplMode::DENY_REPL), hypRef);
	}
	cout << "\nHYPS:\n" << hyps.show() << endl;
	root = new Hyp(convert_tree(*prop.get()->expr.tree(), ReplMode::DENY_REPL), this);
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
		ostringstream oss;
		oss << "\t<proofs>\n";
		if (Hyp* h = dynamic_cast<Hyp*>(nodes_[index])) {
			for (auto& p : h->proofs) {
				if (ProofExp* pr = dynamic_cast<ProofExp*>(p.get())) {
					rus::Step* step = pr->child->step();
					rus::Proof* proof = make_proof(step, prop.id(), prop.get());
					oss << "\t\t<proof expr=\"" << show(step->expr) << "\">";
					oss << "\t\t<![CDATA[\n";
					proof->write(oss);
					oss << "\n";
					oss << "\t\t]]>\n";
					delete proof;
					oss << "\t\t<substitution>\n";
					oss << "\t\t<![CDATA[\n";
					oss << show(pr->sub);
					oss << "\t\t]]>\n";
					oss << "\t\t</substitution>\n";
					oss << "\t</proof>\n";
				} else if (ProofTop* pr = dynamic_cast<ProofTop*>(p.get())) {
					oss << "\t\t<proof expr=\"" << show(pr->expr) << "\">";
					oss << "<![CDATA[";
					oss << "hyp " << pr->hyp.ind + 1;
					oss << "]]>\n";
					oss << "\t\t<substitution>\n";
					oss << "\t\t<![CDATA[\n";
					oss << show(pr->sub);
					oss << "\t\t]]>\n";
					oss << "\t\t</substitution>\n";
					oss << "\t</proof>\n";
				}
			}
		} else if (Prop* pr = dynamic_cast<Prop*>(nodes_[index])) {
			for (auto& p : pr->proofs) {
				if (ProofProp* pr = dynamic_cast<ProofProp*>(p.get())) {
					rus::Step* step = pr->step();
					rus::Proof* proof = make_proof(step, prop.id(), prop.get());
					oss << "\t\t<proof expr=\"" << show(step->expr) << "\">";
					oss << "\t\t<![CDATA[\n";
					proof->write(oss);
					oss << "\n";
					oss << "\t\t]]>\n";
					delete proof;
					oss << "\t\t<substitution>\n";
					oss << "\t\t<![CDATA[\n";
					oss << show(pr->sub);
					oss << "\t\t]]>\n";
					oss << "\t\t</substitution>\n";
					oss << "\t</proof>\n";
				}
			}
		}
		oss << "\t</proofs>\n";
		data += oss.str();
	} else if (what == "tree") {
		data += "\t<tree>\n";
		// TODO
		data += "\t</tree>\n";
	} else if (what == "all") {
		for (auto n : nodes_) {
			data += "\t<node>\n";
			data += Indent::paragraph(n->show(), "\t\t") + "\n";
			data += "\t</node>\n";
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

Return Space::expand(uint index) {
	if (index >= nodes_.size()) {
		cout << index << " OUT OF BOUNDARIES" << endl;
		return false;
	}
	if (Prop* p = dynamic_cast<Prop*>(nodes_[index])) {
		if (p->premises.size() < p->prop.ass->arity()) {
			set<uint> to_show;
			p->buildUp();
			for (auto& h : p->premises) {
				Hyp* hyp = h.get();
				hyp->buildUp();
				add_shown(shown, to_show, hyp);
			}
			ostringstream oss;
			Proved prov = proved();
			if (prov.size()) {
				oss << "<proved>\n";
				for (auto& p : prov) {
					oss << "\t<proof>\n";
					oss << "\t<![CDATA[\n";
					p->write(oss);
					oss << "\t]]>\n";
					oss << "\t</proof>\n";
				}
				oss << "</proved>\n";
			} else {
				oss << "<new>\n";
				for (uint i : to_show) {
					oss << Indent::paragraph(nodes_.at(i)->show()) + "\n";
				}
				oss << "</new>\n";
			}
			cout << endl << oss.str() << endl;
			return Return("node expanded", oss.str(), true);
		}
	} else {
		cout << index << " NOT A PROP" << endl;
	}
	return true;
}

Return Space::prove() {
	Proved prov = doProve();
	if (prov.size()) {
		ostringstream oss;
		oss << "<proved>\n";
		for (auto& p : prov) {
			oss << "\t<proof>\n";
			oss << "\t<![CDATA[\n";
			p->write(oss);
			oss << "\t]]>\n";
			oss << "\t</proof>\n";
		}
		oss << "</proved>\n";
		return Return("successfully proved", oss.str());
	} else {
		return Return("proof not found");
	}
}

Return Space::erase(uint index) {
	if (index >= nodes_.size()) return false;
	delete nodes_[index];
	return true;
}

Space::Proved Space::doProve() {
	while (Prop* p = tactic_->next()) {
		p->buildUp();
		for (auto& h : p->premises) {
			h.get()->buildUp();
		}
		Proved prov = proved();
		if (prov.size()) {
			return prov;
		}
	}
	return Proved();
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
			if (rus::Proof* pr = make_proof(h->child->step(), prop.ass->id(), prop.get())) {
				ret.emplace_back(pr);
			}
		} else if (ProofTop* h = dynamic_cast<ProofTop*>(p.get())) {
			//if (rus::Proof* pr = make_proof(h->child->step(), prop.ass->id(), prop.get())) {
			//	ret.emplace_back(pr);
			//}
			// TODO
		}
	}
	return ret;
}

}}}

