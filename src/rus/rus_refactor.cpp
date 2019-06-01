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

void verify_sub_proof(const SubProof::Node* n) {
	if (n) {
		const Step* s = n->label();
		for (uint i = 0; i < s->refs.size(); ++i) {
			if (const SubProof::Node* c = n->getChild(i)) {
				const Step* ch1 = (s->refs[i]->kind() == Ref::STEP) ? s->refs[i]->step() : nullptr;
				const Step* ch2 = c->label();
				if (ch1 != ch2) {
					throw Error("WRONG: verify_sub_proof: " + n->show([](const Step* s) { return to_string(s->ind()) + ":" + Lex::toStr(s->ass_id()); }));
				}
				verify_sub_proof(n->getChild(i));
			}
		}
	}
}

void verify_sub_proof(const SubProof& sp) {
	verify_sub_proof(sp.getRoot(0));
}

struct SubProofSet {
	string show() const {
		string ret;
		for (const auto& sp : subproofs_) {
			ret += "\t[" +
				Lex::toStr(sp.getRoot(0)->label()->proof()->theorem()->id()) + "] " +
				sp.getRoot(0)->show([](const Step* s) { return to_string(s->ind()) + ":" + Lex::toStr(s->ass_id()); }) +
				"\n";
		}
		return ret;
	}
	uint volume() const {
		return subproofs_.size() - 1;
	}
	void add(SubProof&& sp) {
		//verify_sub_proof(sp);
		auto it = std::lower_bound(subproofs_.begin(), subproofs_.end(), sp);
		if (it == subproofs_.end() || *it != sp) {
			subproofs_.emplace(it, sp);
		}
	}
	void add(const SubProof& sp) {
		//verify_sub_proof(sp);
		auto it = std::lower_bound(subproofs_.begin(), subproofs_.end(), sp);
		if (it == subproofs_.end() || *it != sp) {
			subproofs_.emplace(it, sp);
		}
	}
	const vector<SubProof>& subproofs() const { return subproofs_; }

private:
	vector<SubProof> subproofs_;
};

struct ProofImpls {
	ProofImpls(uint l, const vector<const Step*>& steps) : proof_(l, steps[0]->refs.size()) {
		for (auto s : steps) {
			impls_.add(SubProof(s, s->refs.size()));
		}
	}
	ProofImpls(const ProofImpls& pi) : proof_(pi.proof_) { }

	string show() const {
		string ret;
		ret += "volume: " + to_string(volume()) +  "\n";
		ret += "abstract:\n\t" + proof_.getRoot(0)->show([](uint l) { return Lex::toStr(l); }) + "\n";
		ret += "impls:\n";
		ret += impls_.show();
		return ret;
	}
	uint volume() const {
		return (proof_.size() - 1) * impls_.volume();
	}
	bool operator < (const ProofImpls& pi) const {
		     if (volume() < pi.volume()) return true;
		else if (pi.volume() < volume()) return false;
		else return proof_ < pi.proof_;
	}

	AbstProof proof_;
	SubProofSet impls_;
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

	ProofImpls* getOld(uint i) {
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
	const vector<unique_ptr<ProofImpls>>& old() const {
		return old_;
	}
	const vector<unique_ptr<ProofImpls>>& _new() const {
		return new_;
	}

private:
	void add(ProofImpls* pi, vector<unique_ptr<ProofImpls>>& vect) {
		auto it = std::lower_bound(
			vect.begin(),
			vect.end(), pi,
			[](auto& x, ProofImpls* y) { return *x < *y; }
		);
		if (it != vect.end() && (*it)->proof_ == pi->proof_) {
			for (const auto& sp : pi->impls_.subproofs()) {
				(*it)->impls_.add(sp);
			}
			delete pi;
		} else {
			vect.emplace(it, pi);
		}
		if (vect.size() > max_size) {
			vect.erase(vect.begin());
		}
	}

	vector<unique_ptr<ProofImpls>> old_;
	vector<unique_ptr<ProofImpls>> new_;
	vector<unique_ptr<ProofImpls>> all_;
};

static ProofImplsSet init_subproofs(const AssertionMap& ass_map, uint max_size) {
	ProofImplsSet ret(max_size);
	for (auto& p : ass_map) {
		ret.addNew(new ProofImpls(p.first, p.second));
	}
	return ret;
}

static vector<ProofImpls*> expand_subproof(ProofImpls* pi);

static vector<ProofImpls*> expand_subproof(ProofImpls* pi, uint leaf_ind, SubProof::Leaf leaf, const Step* ch) {
	SubProofSet new_impls;
	for (const SubProof& sp : pi->impls_.subproofs()) {
		const SubProof::Node* ln = sp.getLeaf(leaf_ind).node;
		const auto& r = ln->label()->refs.at(leaf.ind);
		if (const Step* lst = r->step()) {
			if (ch->ass_id() == lst->ass_id()) {
				SubProof new_sp(sp);
				new_sp.expandLeaf(leaf_ind, lst, lst->refs.size());
				new_impls.add(std::move(new_sp));
			}
		}
	}
	if (new_impls.subproofs().size() == 0) {
		throw Error("WRONG: new_impls.size() == 0");
	}
	if (new_impls.subproofs().size() > 1) {
		/*if (new_impls.subproofs().size() == pi->impls_.subproofs().size()) {
			pi->proof_.expandLeaf(leaf_ind, ch->ass_id(), ch->refs.size());
			pi->impls_ = std::move(new_impls);
			return expand_subproof(pi);
		} else {*/
			ProofImpls* new_pi = new ProofImpls(*pi);
			new_pi->proof_.expandLeaf(leaf_ind, ch->ass_id(), ch->refs.size());
			new_pi->impls_ = std::move(new_impls);
			return {new_pi};
		//}
	}
	return {};
}

static vector<ProofImpls*> expand_subproof(ProofImpls* pi) {
	vector<ProofImpls*> ret;
	for (const SubProof& subproof: pi->impls_.subproofs()) {
		for (uint j = 0; j < subproof.leafSize(); ++ j) {
			SubProof::Leaf leaf = subproof.getLeaf(j);
			if (const Step* step = leaf.node->label()) {
				const auto& r = step->refs.at(leaf.ind);
				if (const Step* ch = r->step()) {
					for (ProofImpls* expanded : expand_subproof(pi, j, leaf, ch)) {
						ret.push_back(expanded);
					}
				}
			}
		}
	}
	return ret;
}

static void next_subproofs(ProofImplsSet& pis) {
	for (uint i = 0; i < pis.oldSize(); ++ i) {
		for (ProofImpls* expanded : expand_subproof(pis.getOld(i))) {
			pis.addNew(expanded);
		}
	}
}

}

void factorize_subproofs(const string& opts) {
	AssertionMap ass_map = init_assertion_map();
	auto parsed_opts = parse_options(opts);
	uint max_size = parsed_opts.count("max_subproof_size") ? std::stoul(parsed_opts.at("max_subproof_size")) : ass_map.size();
	cout << "max_size: " << max_size << endl;

	ProofImplsSet common_subproofs = init_subproofs(ass_map, max_size);
	common_subproofs.makeNewOld();
	uint c = 0;
	Timer timer;
	while (true) {
		cout << ++c << ": TO ANALYZE: " << common_subproofs.oldSize() << endl;
		next_subproofs(common_subproofs);
		cout << "ADDED: " << common_subproofs.newSize() << endl;
		if (common_subproofs.newSize()) {
			common_subproofs.makeNewOld();
			cout << "volume: " << common_subproofs.volume() << endl;
			cout << "max. volume: " << endl << common_subproofs.old().back()->show() << endl;
			cout << "min. volume: " << endl << common_subproofs.old().front()->show() << endl;
			cout << "avg. volume: " << double(common_subproofs.volume()) / common_subproofs.oldSize() << endl;
			cout << endl;
		} else {
			cout << "volume: " << common_subproofs.volume() << endl;
			cout << "max. volume: " << endl << common_subproofs.old().back()->show() << endl;
			cout << "min. volume: " << endl << common_subproofs.old().front()->show() << endl;
			cout << "avg. volume: " << double(common_subproofs.volume()) / common_subproofs.oldSize() << endl;
			cout << endl;
			break;
		}
		timer.stop();
		if (timer.getMinutes() > 2.0) {
			break;
		}
	}
	cout << "first 10 max volume: " << endl;
	for (uint i = 0; i < 10; ++ i) {
		cout << common_subproofs.all().at(common_subproofs.all().size() - i - 1)->show() << endl;
	}
	cout << "first 10 min volume: " << endl;
	uint start = 0;
	while (common_subproofs.all().at(start++)->volume() == 0);
	cout << "starts at index: " << start << endl;
	for (uint i = start; i < start + 10; ++ i) {
		cout << common_subproofs.all().at(i)->show() << endl;
	}
	cout << "all volumes: " << endl;
	for (uint i = 0; i < common_subproofs.all().size() - start; ++ i) {
		cout << common_subproofs.all().at(common_subproofs.all().size() - i - 1)->volume() << endl;
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
