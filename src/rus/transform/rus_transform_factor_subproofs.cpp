#include <rus_ast.hpp>
#include <rus/prover/rus_prover_maker.hpp>
#include <dag.hpp>

namespace mdl { namespace rus { namespace {

typedef map<uint, vector<const Step*>> AssertionMap;

AssertionMap init_assertion_map() {
	AssertionMap ass_map;
	for (Assertion& a : Sys::mod().math.get<Assertion>()) {
		if (Theorem* thm = dynamic_cast<Theorem*>(&a)) {
			if (Proof* proof = thm->proof.get()) {
				for (const auto& step : proof->steps) {
					ass_map[step->ass_id()].push_back(step.get());
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
				Lex::toStr(sp.getRoot(0)->label()->proof()->theorem->id()) + "] " +
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

int new_gen_id() {
	static uint i = 0;
	auto gen_id = [](uint ind) { return Lex::toInt("gen_" + to_string(ind) + "_th"); };
	while (Sys::get().math.get<Assertion>().has(gen_id(i))) i += 1;
	return gen_id(i);
}

static unique_ptr<Theorem> generate_theorem(const AbstProof& aproof) {
	try {
		unique_ptr<Theorem> ret = prover::make_theorem(aproof, new_gen_id());
		if (ret) {
			cout << "maker succeeded" << endl;
		} else {
			cout << "maker failed" << endl;
			exit(-1);
		}
		return ret;
	} catch (Error& err) {
		err.msg += "\nwhile generating from proof:\n" + aproof.show([](uint l) { return Lex::toStr(l); }) + "\n";
		throw err;
	}
	return nullptr;
}

}

struct AbstProofForest {
	struct Node;
	typedef std::map<uint, Node> Nodes;
	Nodes nodes;

	struct Node {
		Node(uint arity) : children(arity) { }
		Node(const Node&) = default;
		Node(Node&&) = default;
		vector<string> showLines(vector<Nodes::const_iterator>& path) const {
			vector<string> lines;
			for (auto& ch : children) {
				for (auto line : ch.showLines(path)) {
					lines.push_back(line);
				}
				if (proofs.size()) {
					string line;
					for (auto& i : path) {
						line += Lex::toStr(i->first) + " ";
					}
					line += " -> {";
					for (uint p : proofs) {
						line += Lex::toStr(p) + ", ";
					}
					line += "}";
					lines.push_back(line);
				}
			}
			return lines;
		}
		vector<AbstProofForest> children;
		set<uint> proofs;
	};

	vector<string> showLines(vector<Nodes::const_iterator>& path) const {
		vector<string> lines;
		for (auto i = nodes.begin(); i != nodes.end(); ++i) {
			path.push_back(i);
			for (string line : i->second.showLines(path)) {
				lines.push_back(line);
			}
			path.pop_back();
		}
		return lines;
	}
	string show() const {
		vector<Nodes::const_iterator> path;
		vector<string> lines = showLines(path);
		string ret;
		for (auto& line : lines) {
			ret += line + "\n";
		}
		return ret;
	}
	void add(const AbstProof::Node& n, uint id) {
		if (!nodes.count(n.label())) {
			nodes.emplace(n.label(), Node(n.childrenArity()));
		}
		Node& m = nodes.at(n.label());
		bool is_leaf = true;
		for (uint i = 0; i < n.childrenArity(); ++ i) {
			if (n.getChild(i)) {
				is_leaf = false;
				m.children.at(i).add(*n.getChild(i), id);
			}
		}
		if (is_leaf) {
			m.proofs.insert(id);
		}
	}
	void add(const AbstProof& p, uint id) {
		add(*p.getRoot(), id);
	}
	bool collect(const AbstProof::Node& n, unique_ptr<set<uint>>& ids) const {
		if (!nodes.count(n.label())) {
			return false;
		} else {
			const Node& m = nodes.at(n.label());
			bool is_leaf = true;
			for (uint i = 0; i < n.childrenArity(); ++ i) {
				if (n.getChild(i)) {
					is_leaf = false;
					if (!m.children.at(i).collect(*n.getChild(i), ids)) {
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
	unique_ptr<set<uint>> map(AbstProof& p) const {
		unique_ptr<set<uint>> ids;
		collect(*p.getRoot(), ids);
		if (!ids) {
			ids.reset(new set<uint>());
		}
		return ids;
	}
	static AbstProofForest produce() {
		vector<const Assertion*> assertions = Sys::get().math.get<Assertion>().values();
		vector<const Proof*> proofs;
		for (const Assertion* a : assertions) {
			if (const Theorem* thm = dynamic_cast<const Theorem*>(a)) {
				if (const Proof* proof = thm->proof.get()) {
					proofs.push_back(proof);
				}
			}
		}
		AbstProofForest ret;
		for (const Proof* p : proofs) {
			AbstProof aproof = p->abst();
			ret.add(aproof, p->theorem->id());
		}
		return ret;
	}
};

void factorize_subproofs(const string& opts) {
	AssertionMap ass_map = init_assertion_map();
	map<string, string> parsed_opts = parse_options(opts);
	uint max_size = parsed_opts.count("max_subproof_size") ? std::stoul(parsed_opts.at("max_subproof_size")) : ass_map.size();

	ProofImplsSample common_subproofs = init_subproofs(ass_map, max_size);
	common_subproofs.makeNewOld();
	uint c = 0;
	Timer timer;
	while (true) {
		//cout << ++c << ": TO ANALYZE: " << common_subproofs.old_.size() << endl;
		next_subproofs(common_subproofs);
		//cout << "ADDED: " << common_subproofs.new_.size() << endl;
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
	AbstProofForest proofsForest = AbstProofForest::produce();
	uint start = 0;
	while (common_subproofs.all_.set().at(start++)->volume() == 0);
	cout << "common_subproofs.all_.size(): " << common_subproofs.all_.size() << endl;
	cout << "first 10 max volume: " << endl;
	uint inserted_count = 0;
	for (uint i = 0; i < 10; ++ i) {
		ProofImpls* impls = common_subproofs.all_.set().at(common_subproofs.all_.size() - i - 1).get();
		cout << impls->show() << endl;
		//cout << "volume: " << impls->volume() << endl;
		unique_ptr<Theorem> theorem = generate_theorem(impls->proof_);
		if (theorem) {
			beautify(*theorem);
			cout << (theorem ? theorem->show() : "theorem: <null>") << endl;
			unique_ptr<set<uint>> other = proofsForest.map(impls->proof_);
			if (other->size()) {
				cout << "this proof is already in the system: " << endl;
				for (uint id : *other) {
					cout << "\t" << Lex::toStr(id) << endl;
				}
			} else {
				cout << "this proof is new, inserting" << endl;
				insert_theorem(theorem);
				inserted_count += 1;
			}
		}
	}
	cout << "Total number of inserted theorems: " << inserted_count << endl;
	/*cout << "first 10 min volume: " << endl;
	cout << "starts at index: " << start << endl;
	for (uint i = start; i < start + 10; ++ i) {
		ProofImpls* impls = common_subproofs.all_.set().at(i).get();
		cout << impls->show() << endl;
		unique_ptr<Theorem> theorem = generate_theorem(impls->proof_);
		if (theorem) {
			beautify(*theorem);
			cout << (theorem ? theorem->show() : "theorem: <null>") << endl;
		}
	}*/
	/*cout << "all volumes: " << endl;
	for (uint i = start; i < common_subproofs.all_.size(); ++ i) {
		//cout << common_subproofs.all_.set().at(i)->show() << endl;
		cout << common_subproofs.all_.set().at(common_subproofs.all_.size() - i - 1)->volume() << endl;
	}*/
}

}} // mdl::rus
