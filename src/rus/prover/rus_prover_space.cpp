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
	uint c = 0;
	for (auto& p : prop.ass->props) {
		if (!p.get()->expr.tree()) {
			throw Error("unparsed expression", show(p.get()->expr));
		}
		hyps.add(p.get()->expr.tree(), HypRef(a, c++));
	}
	root = new Hyp(std::move(create_non_replaceable(p->expr)), this);
	root->buildUp();
}

Return Space::init() {
	string data;
	shown.insert(root->ind);
	data += "<new>\n";
	data += Indent::paragraph(root->show()) + "\n";
	data += "</new>\n";
	cout << endl << data << endl;
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
	if (index >= nodes_.size()) return false;
	if (Prop* p = dynamic_cast<Prop*>(nodes_[index])) {
		if (p->premises.size() < p->prop.ass->arity()) {
			set<uint> to_show;
			p->buildUp();
			for (auto& h : p->premises) {
				Hyp* hyp = h.get();
				hyp->buildUp();
				add_shown(shown, to_show, hyp);
			}
			string data;
			data += "<new>\n";
			for (uint i : to_show) {
				data += Indent::paragraph(nodes_.at(i)->show()) + "\n";
			}
			data += "</new>\n";
			cout << endl << data << endl;
			return Return("node expanded", data);
		}
	}
	return true;
}

Return Space::erase(uint index) {
	if (index >= nodes_.size()) return false;
	if (Prop* p = dynamic_cast<Prop*>(nodes_[index])) {
		// TODO
	}
	return true;
}

rus::Proof* Space::prove() {
	while (Prop* p = tactic_->next()) {
		p->buildUp();
		for (auto& h : p->premises) {
			h.get()->buildUp();
		}
		if (rus::Proof* ret = checkProved()) {
			return ret;
		}
	}
	return nullptr;
}

void delete_steps_recursively(rus::Step* s) {
	for (auto& r : s->refs) {
		if (r.get()->kind() == rus::Ref::STEP) {
			delete_steps_recursively(r.get()->step());
		}
	}
	delete s;
}

rus::Proof* Space::checkProved() {
	if (!root->proofs.size()) return nullptr;
	for (auto& p : root->proofs) {
		if (ProofProp* ps = dynamic_cast<ProofProp*>(p.get())) {
			rus::Step* s = ps->step();
			if (rus::Proof* pr = make_proof(s, prop.ass->id(), prop.get())) {
				if (pr->check()) return pr;
			}
			delete_steps_recursively(s);
		}
	}
	root->proofs.clear();
	return nullptr;
}

Space* Space::instance = nullptr;

}}}

