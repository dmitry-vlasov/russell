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

struct ProofImpls {
	ProofImpls(uint l, const Step* s) : proof(l, s->refs.size()) {
		impls.emplace_back(s, s->refs.size());
	}
	ProofImpls(uint l, const vector<const Step*>& steps) : proof(l, steps[0]->refs.size()) {
		for (auto s : steps) {
			impls.emplace_back(s, s->refs.size());
		}
	}
	ProofImpls(const ProofImpls& pi) : proof(pi.proof) { }

	string show() const {
		string ret;
		ret += "volume: " + to_string(volume()) +  "\n";
		ret += "abstract:\n\t" + proof.getRoot(0)->show([](uint l) { return Lex::toStr(l); }) + "\n";
		ret += "impls:\n";
		for (const auto& im : impls) {
			ret += "\t" + im.getRoot(0)->show([](const Step* s) { return "S:" + Lex::toStr(s->ass_id()); }) + "\n";
		}
		return ret;
	}
	uint volume() const {
		return (proof.size() - 1) * (impls.size() - 1);
	}
	bool operator < (const ProofImpls& pi) const {
		return volume() < pi.volume();
	}

	AbstProof proof;
	vector<SubProof> impls;
	bool was_tested = false;
};

struct ProofImplsSet {
	ProofImplsSet(uint ms) : max_size(ms) {
		old_.reserve(max_size + 1);
		new_.reserve(max_size + 1);
		all_.reserve(max_size + 1);
	}
	const uint max_size;

	void addNew(ProofImpls* pi) {
		add(pi, new_);
	}
	void makeNewOld() {
		for (auto& o : old_) {
			add(o.release(), all_);
		}
		old_ = std::move(new_);
	}
	uint volume() const {
		return std::accumulate(
			old_.begin(),
			old_.end(), 0,
			[](uint a, auto& pi) { return a + pi->volume(); }
		);
	}

	const ProofImpls* get(uint i) const {
		return old_.at(i).get();
	}
	uint oldSize() const {
		return old_.size();
	}
	uint newSize() const {
		return new_.size();
	}
	const vector<unique_ptr<ProofImpls>>& all() const {
		return all_;
	}

private:
	void add(ProofImpls* pi, vector<unique_ptr<ProofImpls>>& vect) {
		auto it = std::lower_bound(
			vect.begin(),
			vect.end(), pi,
			[](auto& x, ProofImpls* y) { return x->volume() < y->volume(); }
		);
		vect.emplace(it, pi);
		if (vect.size() > max_size) {
			vect.erase(vect.begin());
		}
	}

	vector<unique_ptr<ProofImpls>> old_;
	vector<unique_ptr<ProofImpls>> new_;
	vector<unique_ptr<ProofImpls>> all_;
};

ProofImplsSet init_subproofs(const AssertionMap& ass_map, uint max_size) {
	ProofImplsSet ret(max_size);
	for (auto& p : ass_map) {
		ret.addNew(new ProofImpls(p.first, p.second));
	}
	return ret;
}

ProofImpls* try_to_expand(const ProofImpls* pi, uint subproof_ind, uint leaf_ind, SubProof::Leaf leaf, uint ref_ind, const Step* ch, const AssertionMap& ass_map) {
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
		ProofImpls* new_pi = new ProofImpls(*pi);
		new_pi->proof.expandLeaf(leaf_ind, ch->ass_id(), ch->refs.size());
		new_pi->impls = std::move(new_impls);
		return new_pi;
	} else {
		return nullptr;
	}
}

void next_subproofs(ProofImplsSet& pis, const AssertionMap& ass_map) {
	uint c = 0;
	for (uint i0 = 0; i0 < pis.oldSize(); ++ i0) {
		const ProofImpls* pi = pis.get(i0);
		for (uint i = 0; i < pi->impls.size(); ++i) {
			const SubProof& subproof = pi->impls.at(i);
			for (uint j = 0; j < subproof.leafSize(); ++ j) {
				SubProof::Leaf leaf = subproof.getLeaf(j);
				const Step* step = leaf.node->label();
				for (uint k = 0; k < step->refs.size(); ++k) {
					const auto& r = step->refs.at(k);
					if (r->kind() == Ref::STEP) {
						const Step* ch = r->step();
						if (ProofImpls* ni = try_to_expand(pi, i, j, leaf, k, ch, ass_map)) {
							++c;
							if (!(c % 100000)) {
								cout << "c: " << ++c << endl;
								cout << "pi.volume: " << pi->volume() << endl;
								cout << "ni.volume: " << ni->volume() << endl;
								cout << "pis.oldSize: " << pis.oldSize() << endl;
								cout << "pis.newSize: " << pis.newSize() << endl;
								cout << "pis.volume: " << pis.volume() << endl;
								cout << "pis.avg. volume: " << double(pis.volume()) / pis.oldSize() << endl;
							}
							pis.addNew(ni);
						}
					}
				}
			}
		}
	}
}

}

void factorize_subproofs(const string& opts) {
	AssertionMap ass_map = init_assertion_map();
	//cout << "ass_map.size() = " << ass_map.size() << endl;

	auto parsed_opts = parse_options(opts);
	uint max_size = parsed_opts.count("max_subproof_size") ? std::stoul(parsed_opts.at("max_subproof_size")) : 10000;
	cout << "max_size = " << max_size << endl;

	ProofImplsSet common_subproofs = init_subproofs(ass_map, max_size);
	common_subproofs.makeNewOld();
	uint c = 0;
	while (true) {
		cout << ++c << ": TO ANALYZE: " << common_subproofs.oldSize() << endl;
		next_subproofs(common_subproofs, ass_map);
		cout << "ADDED: " << common_subproofs.newSize() << endl;
		cout << "volume: " << common_subproofs.volume() << endl;
		cout << "avg. volume: " << double(common_subproofs.volume()) / common_subproofs.oldSize() << endl;
		if (common_subproofs.newSize()) {
			common_subproofs.makeNewOld();
		} else {
			break;
		}
	}
	cout << "first 10 max volume: " << endl;
	for (uint i = 0; i < 10; ++ i) {
		cout << common_subproofs.all().at(common_subproofs.all().size() - i - 1)->show() << endl;
	}
	cout << "first 10 min volume: " << endl;
	for (uint i = 0; i < 10; ++ i) {
		cout << common_subproofs.all().at(i)->show() << endl;
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
