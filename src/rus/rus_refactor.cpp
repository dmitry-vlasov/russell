#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include "../../include/dag.hpp"

namespace mdl { namespace rus { namespace {

void reduce_duplcate_steps(Proof* proof) {
	vector<Proof::Elem> new_elems;
	prover::unify::Index expressions;
	vector<Step*> new_steps;
	map<const Step*, Step*> steps_map;
	for (auto& e : proof->elems) {
		switch (Proof::kind(e)) {
		case Proof::STEP: {
			const Step* step = Proof::step(e);
			prover::Term term = prover::Tree2Term(*step->expr.tree());
			const vector<uint>* previous = expressions.find(term);
			if (previous && previous->size()) {
				steps_map[step] = new_steps.at(previous->at(0));
			} else {
				uint new_ind = new_steps.size();
				Step* new_step = new Step(
					new_ind, step->kind(), step->ass_id(), step->proof_, step->token
				);
				new_step->expr = std::move(step->expr);
				new_step->sub = std::move(step->sub);
				for (const auto& ref : step->refs) {
					switch (ref->kind()) {
					case Ref::HYP:  new_step->refs.emplace_back(make_unique<Ref>(ref->hyp(), ref->token)); break;
					case Ref::PROP: new_step->refs.emplace_back(make_unique<Ref>(ref->prop(), ref->token)); break;
					case Ref::STEP: new_step->refs.emplace_back(make_unique<Ref>(steps_map.at(ref->step()), ref->token)); break;
					}
				}
				expressions.add(term, new_ind);
				steps_map[step] = new_step;
				new_steps.push_back(new_step);
				new_elems.emplace_back(unique_ptr<Step>(new_step));
			}
			break;
		}
		case Proof::QED: {
			const Qed* qed = Proof::qed(e);
			new_elems.emplace_back(make_unique<Qed>(qed->prop, steps_map.at(qed->step))); break;
		}
		case Proof::VARS: {
			new_elems.push_back(std::move(e)); break;
		}
		}
	}
	if (new_elems.size() < proof->elems.size()) {
		//cout << "diff: " << (proof->elems.size() - new_elems.size()) << ", new_elems.size() = " << new_elems.size() << " < " << proof->elems.size() << " = proof->elems.size()" << endl;
		proof->elems = std::move(new_elems);
	}
}



typedef map<uint, vector<const Step*>> AssertionMap;

AssertionMap init_assertion_map() {
	AssertionMap ass_map;
	for (auto& p : Sys::mod().math.get<Proof>()) {
		if (Proof* proof = p.second.data) {
			for (const auto& e : proof->elems) {
				if (Proof::kind(e) == Proof::STEP) {
					const Step* step = Proof::step(e);
					ass_map[step->ass_id()].push_back(step);
				}
			}
		}
	}
	return ass_map;
}

typedef DAG<uint> AbstProof;
typedef DAG<const Step*> SubProof;

struct ProofImpl {
	ProofImpl(uint l, const Step* s) : abst(l, s->refs.size()) {
		impls.emplace_back(s, s->refs.size());
	}
	ProofImpl(uint l, const vector<const Step*>& steps) : abst(l, steps[0]->refs.size()) {
		for (auto s : steps) {
			impls.emplace_back(s, s->refs.size());
		}
	}
	ProofImpl(const ProofImpl& pi) : abst(pi.abst) { }

	string show() const {
		string ret;
		ret += "abstract:\n\t" + abst.getRoot(0)->show([](uint l) { return Lex::toStr(l); }) + "\n";
		ret += "impls:\n";
		for (const auto& im : impls) {
			ret += "\t" + im.getRoot(0)->show([](const Step* s) { return "S:" + Lex::toStr(s->ass_id()); }) + "\n";
		}
		return ret;
	}

	AbstProof abst;
	vector<SubProof> impls;
	bool was_tested = false;
};

vector<unique_ptr<ProofImpl>> init_subproofs(const AssertionMap& ass_map) {
	vector<unique_ptr<ProofImpl>> ret;
	for (auto& p : ass_map) {
		uint ass_id = p.first;
		ret.emplace_back(make_unique<ProofImpl>(ass_id, p.second));
		//cout << ret.back()->show() << endl;
	}
	return ret;
}

ProofImpl* try_to_expand(const ProofImpl* pi, uint subproof_ind, uint leaf_ind, SubProof::Leaf leaf, uint ref_ind, const Step* ch, const AssertionMap& ass_map) {
	vector<SubProof> new_impls;
	for (const SubProof& sp : pi->impls) {
		const SubProof::Node* ln = sp.getLeaf(leaf_ind).node;
		const auto& r = ln->label()->refs.at(ref_ind);
		if (r->kind() == Ref::STEP) {
			const Step* lst = r->step();
			if (ch->ass_id() == lst->ass_id()) {
				new_impls.emplace_back(sp);
				new_impls.back().expandLeaf(leaf_ind, lst, lst->refs.size());
			}
		}
	}
	if (new_impls.size() == 0) {
		throw Error("WRONG: new_impls.size() == 0");
	}
	if (new_impls.size() > 1) {
		ProofImpl* new_pi = new ProofImpl(*pi);
		new_pi->abst.expandLeaf(leaf_ind, ch->ass_id(), ch->refs.size());
		new_pi->impls = std::move(new_impls);
		//cout << new_pi->show() << endl;
		return new_pi;
	} else {
		return nullptr;
	}
}

bool next_subproofs(uint start, vector<unique_ptr<ProofImpl>>& v, const AssertionMap& ass_map) {
	bool ret = false;
	for (uint i0 = start; i0 < v.size(); ++i0) {
		const ProofImpl* pi = v.at(i0).get();
		for (uint i = 0; i < pi->impls.size(); ++i) {
			const SubProof& subproof = pi->impls.at(i);
			for (uint j = 0; j < subproof.leafSize(); ++ j) {
				SubProof::Leaf leaf = subproof.getLeaf(j);
				const Step* step = leaf.node->label();
				for (uint k = 0; k < step->refs.size(); ++k) {
					const auto& r = step->refs.at(k);
					if (r->kind() == Ref::STEP) {
						const Step* ch = r->step();
						if (ProofImpl* ni = try_to_expand(pi, i, j, leaf, k, ch, ass_map)) {
							v.emplace_back(ni);
							ret = true;
						}
					}
				}
			}
		}
	}
	return ret;
}

}

void factorize_subproofs() {
	AssertionMap ass_map = init_assertion_map();
	cout << "ass_map.size() = " << ass_map.size() << endl;
	vector<unique_ptr<ProofImpl>> common_subproofs = init_subproofs(ass_map);
	uint start = 0;
	while (true) {
		uint new_start = common_subproofs.size();
		cout << "TO ANALYZE: " << new_start << endl;
		if (next_subproofs(start, common_subproofs, ass_map)) {
			cout << "ADDED: " << common_subproofs.size() - new_start << endl;
			start = new_start;
		} else {
			break;
		}
	}
}

#ifdef PARALLEL
#define PARALLEL_DUPLICATE_STEPS
#endif

void reduce_duplcate_steps()  {
	vector<Proof*> proofs;
	for (auto& p : Sys::mod().math.get<Proof>()) {
		if (Proof* proof = p.second.data) {
			proofs.push_back(proof);
		}
	}
#ifdef PARALLEL_DUPLICATE_STEPS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[&proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_duplcate_steps(proofs[i]);
			}
		}
	);
#else
	for (auto proof : proofs) {
		reduce_duplcate_steps(proof);
	}
#endif
}

}} // mdl::rus
