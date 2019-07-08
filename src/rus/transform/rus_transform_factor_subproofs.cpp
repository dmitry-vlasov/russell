#include <rus_ast.hpp>
#include <rus/prover/rus_prover_maker.hpp>
#include <dag.hpp>

namespace mdl { namespace rus { namespace {

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
	bool to_remove = false;
};

struct ProofImplsSet {
	ProofImplsSet(uint ms, bool reserve_vect = false) : max_size(ms) {
		if (reserve_vect) {
			set_.reserve(max_size + 1);
		}
	}
	ProofImplsSet(ProofImplsSet&&) = default;
	ProofImplsSet& operator = (ProofImplsSet&&) = default;

	uint max_size;

	uint volume() const {
		return std::accumulate(
			set_.begin(),
			set_.end(), 0,
			[](uint a, auto& pi) { return a + pi->volume(); }
		);
	}

	ProofImpls* get(uint i) {
		return set_.at(i).get();
	}
	uint size() const {
		return set_.size();
	}
	const vector<unique_ptr<ProofImpls>>& set() const {
		return set_;
	}
	vector<unique_ptr<ProofImpls>>& set() {
		return set_;
	}

	void add(ProofImpls* pi) {
		auto it = std::lower_bound(
			set_.begin(),
			set_.end(), pi,
			[](auto& x, ProofImpls* y) { return *x < *y; }
		);
		if (it != set_.end() && (*it)->proof_ == pi->proof_) {
			for (const auto& sp : pi->impls_.subproofs()) {
				(*it)->impls_.add(sp);
			}
			delete pi;
		} else {
			set_.emplace(it, pi);
		}
		if (set_.size() > max_size) {
			set_.erase(set_.begin());
		}
	}

	string show() const {
		string ret;
		for (const auto& pi : set_) {
			ret += pi->show() + "\n";
		}
		return ret;
	}

private:
	vector<unique_ptr<ProofImpls>> set_;
};

struct ProofImplsSample {
	ProofImplsSample(uint max_size) :
		old_(max_size, true),
		new_(max_size, true),
		all_(max_size, true) { }

	void makeNewOld() {
		for (auto& o : old_.set()) {
			if (!o->to_remove) {
				all_.add(o.release());
			}
		}
		old_ = std::move(new_);
	}

	ProofImplsSet old_;
	ProofImplsSet new_;
	ProofImplsSet all_;
};

static ProofImplsSample init_subproofs(const AssertionMap& ass_map, uint max_size) {
	ProofImplsSample ret(max_size);
	for (auto& p : ass_map) {
		ret.new_.add(new ProofImpls(p.first, p.second));
	}
	return ret;
}

//static ProofImplsSet expand_subproof(ProofImpls* pi, uint i);

static ProofImpls* expand_subproof_impl_leaf(ProofImpls* pi, uint i, uint leaf_ind, SubProof::Leaf leaf, const Step* ch) {
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
		ProofImpls* new_pi = new ProofImpls(*pi);
		new_pi->proof_.expandLeaf(leaf_ind, ch->ass_id(), ch->refs.size());
		new_pi->impls_ = std::move(new_impls);
		return new_pi;
	} else {
		return nullptr;
	}
}

static vector<ProofImpls*> expand_subproof_impl(ProofImpls* pi, uint i) {
	vector<ProofImpls*> ret;
	const SubProof& subproof = pi->impls_.subproofs().at(i);
	for (uint j = 0; j < subproof.leafSize(); ++ j) {
		SubProof::Leaf leaf = subproof.getLeaf(j);
		if (const Step* step = leaf.node->label()) {
			if (const auto& r = step->refs.at(leaf.ind)) {
				if (const Step* ch = r->step()) {
					if (ProofImpls* expanded = expand_subproof_impl_leaf(pi, i, j, leaf, ch)) {
						ret.push_back(expanded);
					}
				}
			}
		}
	}
	return ret;
}

static ProofImpls* expand_subproof_impl_leaf_total(ProofImpls* pi, uint leaf_ind, SubProof::Leaf leaf, const Step* ch) {
	SubProofSet new_impls;
	for (const SubProof& sp : pi->impls_.subproofs()) {
		const SubProof::Node* ln = sp.getLeaf(leaf_ind).node;
		const auto& r = ln->label()->refs.at(leaf.ind);
		if (const Step* lst = r->step()) {
			if (ch->ass_id() == lst->ass_id()) {
				SubProof new_sp(sp);
				new_sp.expandLeaf(leaf_ind, lst, lst->refs.size());
				new_impls.add(std::move(new_sp));
			} else {
				return nullptr;
			}
		} else {
			return nullptr;
		}
	}
	ProofImpls* new_pi = new ProofImpls(*pi);
	new_pi->proof_.expandLeaf(leaf_ind, ch->ass_id(), ch->refs.size());
	new_pi->impls_ = std::move(new_impls);
	return new_pi;
}

static ProofImpls* expand_subproof_impl_total(ProofImpls* pi, bool initial = true) {
	const SubProof& subproof = pi->impls_.subproofs().at(0);
	for (uint j = 0; j < subproof.leafSize(); ++ j) {
		SubProof::Leaf leaf = subproof.getLeaf(j);
		if (const Step* step = leaf.node->label()) {
			if (const auto& r = step->refs.at(leaf.ind)) {
				if (const Step* ch = r->step()) {
					if (ProofImpls* expanded = expand_subproof_impl_leaf_total(pi, j, leaf, ch)) {
						if (!initial) {
							delete pi;
						}
						return expand_subproof_impl_total(expanded, false);
					}
				}
			}
		}
	}
	return initial ? nullptr : pi;
}


static vector<ProofImpls*> expand_subproof(ProofImpls* pi) {
	vector<ProofImpls*> ret;
	if (ProofImpls* exp_pi = expand_subproof_impl_total(pi)) {
		ret.push_back(exp_pi);
	} else {
		for (uint i = 0 ; i < pi->impls_.subproofs().size(); ++i) {
			for (ProofImpls* expanded : expand_subproof_impl(pi, i)) {
				ret.push_back(expanded);
			}
		}
	}
	return ret;
}

static void next_subproofs(ProofImplsSample& pis) {
	for (uint i = 0; i < pis.old_.size(); ++ i) {
		for (ProofImpls* expanded : expand_subproof(pis.old_.get(i))) {
			pis.new_.add(expanded);
		}
	}
}


static pair<unique_ptr<Theorem>, unique_ptr<Proof>> generate_theorem(const AbstProof& aproof) {
	pair<unique_ptr<Theorem>, unique_ptr<Proof>> ret;
	static uint i = 0;
	prover::Maker maker(aproof, Lex::toInt("gen_" + to_string(i++) + "_th"));
	try {
		unique_ptr<prover::Thm> r = maker.make();
		if (r) {
			//ret.second = std::move(maker.proved()[0]);
			//ret.first = std::move(maker.theorem_);
			cout << "maker succeeded" << endl;
			//cout << r->show() << endl;
			ret.first = r->theorem();
			ret.second = std::move(r->proof);
		} else {
			cout << "maker failed" << endl;

			//cout << "oracle test failed" << endl;
			cout << "maker status:" << endl;
			cout << maker.tactic()->show() << endl;
			//cout << "FAILED ";
			//cout << "original abst proof:" << endl;
			//cout << *p << endl;
			exit(-1);
		}
	} catch (Error& err) {
		cout << "prover theorem: " << endl;
		//cout << maker.theorem_->show() << endl;
		throw err;
	}
	return ret;
}

}

void factorize_subproofs(const string& opts) {
	AssertionMap ass_map = init_assertion_map();
	auto parsed_opts = parse_options(opts);
	uint max_size = parsed_opts.count("max_subproof_size") ? std::stoul(parsed_opts.at("max_subproof_size")) : ass_map.size();
	cout << "max_size: " << max_size << endl;

	ProofImplsSample common_subproofs = init_subproofs(ass_map, max_size);
	common_subproofs.makeNewOld();
	uint c = 0;
	Timer timer;
	while (true) {
		cout << ++c << ": TO ANALYZE: " << common_subproofs.old_.size() << endl;
		next_subproofs(common_subproofs);
		cout << "ADDED: " << common_subproofs.new_.size() << endl;
		if (common_subproofs.new_.size()) {
			common_subproofs.makeNewOld();
			/*cout << "old  volume: " << common_subproofs.old_.volume() << endl;
			cout << "max. volume: " << endl << common_subproofs.old_.set().back()->show() << endl;
			cout << "min. volume: " << endl << common_subproofs.old_.set().front()->show() << endl;
			cout << "avg. volume: " << double(common_subproofs.old_.volume()) / common_subproofs.old_.size() << endl;
			cout << endl;*/
		} else {
			/*cout << "old  volume: " << common_subproofs.old_.volume() << endl;
			cout << "max. volume: " << endl << common_subproofs.old_.set().back()->show() << endl;
			cout << "min. volume: " << endl << common_subproofs.old_.set().front()->show() << endl;
			cout << "avg. volume: " << double(common_subproofs.old_.volume()) / common_subproofs.old_.size() << endl;
			cout << endl;*/
			break;
		}
		timer.stop();
		if (timer.getMinutes() > 2.0) {
			break;
		}
	}
	uint start = 0;
	while (common_subproofs.all_.set().at(start++)->volume() == 0);
	cout << "common_subproofs.all_.size(): " << common_subproofs.all_.size() << endl;
	cout << "first 10 max volume: " << endl;
	for (uint i = 0; i < 10; ++ i) {
		ProofImpls* impls = common_subproofs.all_.set().at(common_subproofs.all_.size() - i - 1).get();
		cout << impls->show() << endl;
		pair<unique_ptr<Theorem>, unique_ptr<Proof>> generated = generate_theorem(impls->proof_);
		cout << (generated.first ? generated.first->show() : "theorem: <null>") << endl;
		cout << (generated.second ? generated.second->show() : "proof: <null>") << endl;
	}
	/*cout << "first 10 min volume: " << endl;
	cout << "starts at index: " << start << endl;
	for (uint i = start; i < start + 10; ++ i) {
		cout << common_subproofs.all_.set().at(i)->show() << endl;
	}
	cout << "all volumes: " << endl;
	for (uint i = start; i < common_subproofs.all_.size(); ++ i) {
		cout << common_subproofs.all_.set().at(i)->show() << endl;
		//cout << common_subproofs.all_.set().at(common_subproofs.all_.size() - i - 1)->volume() << endl;
	}*/
}

}} // mdl::rus
