#include <rus_ast.hpp>
#include <dag.hpp>

namespace mdl { namespace rus {

static void add_to_proof_set(AbstProofSet& ps, const AbstProof::Node& n, uint id) {
	if (!ps.nodes.count(n.label())) {
		ps.nodes.emplace(n.label(), AbstProofSet::Node(n.childrenArity()));
	}
	AbstProofSet::Node& m = ps.nodes.at(n.label());
	bool is_leaf = true;
	for (uint i = 0; i < n.childrenArity(); ++ i) {
		if (n.getChild(i)) {
			is_leaf = false;
			add_to_proof_set(m.children.at(i), *n.getChild(i), id);
		}
	}
	if (is_leaf) {
		m.proofs.insert(id);
	}
}

void AbstProofSet::add(const AbstProof& p, uint id) {
	add_to_proof_set(*this, *p.getRoot(), id);
}

static bool collect_in_proof_set(const AbstProofSet& ps, const AbstProof::Node& n, unique_ptr<set<uint>>& ids) {
	if (!ps.nodes.count(n.label())) {
		return false;
	} else {
		const AbstProofSet::Node& m = ps.nodes.at(n.label());
		bool is_leaf = true;
		for (uint i = 0; i < n.childrenArity(); ++ i) {
			if (n.getChild(i)) {
				is_leaf = false;
				if (!collect_in_proof_set(m.children.at(i), *n.getChild(i), ids)) {
					return false;
				}
			}
		}
		if (is_leaf) {
			if (!ids) {
				ids.reset(new set<uint>());
				for (uint l : m.proofs) {
					ids->insert(l);
				}
			} else {
				vector<uint> to_remove;
				for (uint id : *ids) {
					if (!m.proofs.count(id)) {
						to_remove.push_back(id);
					}
				}
				for (uint id : to_remove) {
					ids->erase(id);
				}
				if (!ids->size()) {
					return false;
				}
			}
		}
		return true;
	}
}

unique_ptr<set<uint>> AbstProofSet::map(AbstProof& p) const {
	unique_ptr<set<uint>> ids;
	collect_in_proof_set(*this, *p.getRoot(), ids);
	if (!ids) {
		ids.reset(new set<uint>());
	}
	return ids;
}

bool AbstProofSet::contains(AbstProof& p) const {
	unique_ptr<set<uint>> ids = map(p);
	return ids->size();
}

AbstProofSet AbstProofSet::produce() {
	vector<const Assertion*> assertions = Sys::get().math.get<Assertion>().values();
	vector<const Proof*> proofs;
	for (const Assertion* a : assertions) {
		if (const Theorem* thm = dynamic_cast<const Theorem*>(a)) {
			if (const Proof* proof = thm->proof.get()) {
				proofs.push_back(proof);
			}
		}
	}
	AbstProofSet ret;
	for (const Proof* p : proofs) {
		AbstProof aproof = p->abst();
		ret.add(aproof, p->theorem->id());
	}
	return ret;
}

}} // mdl::rus
