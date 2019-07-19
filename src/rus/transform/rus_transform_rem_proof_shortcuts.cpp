#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_cartesian.hpp>

namespace mdl { namespace rus { namespace {

typedef prover::unify::IndexMap<PropRef> PropIndex;
typedef prover::unify::IndexMap<HypRef> HypIndex;
typedef prover::unify::IndexMap<Step*> StepIndex;

set<const Writable*> intermediate(const Step* parent, const vector<const Writable*>& children) {
	struct Pair {
		Pair(const Writable* n, const vector<const Writable*>& p = vector<const Writable*>()) :
			node(n), path(p) { }
		Pair(const Pair&) = default;
		const Writable* node;
		vector<const Writable*> path;
	};
	stack<Pair> s;
	s.push(Pair(parent));
	set<const Writable*> ret;
	while (!s.empty()) {
		auto p = s.top(); s.pop();
		if (std::find(children.begin(), children.end(), p.node) != children.end()) {
			for (auto n : p.path) {
				ret.insert(n);
				ret.insert(p.node);
			}
		}
		vector<const Writable*> path(p.path);
		path.push_back(p.node);
		if (const Step* st = dynamic_cast<const Step*>(p.node)) {
			for (auto& r : st->refs) {
				s.push(Pair(r->ref(), path));
			}
		}
	}
	return ret;
}

struct Shortcut {
	struct Longcut {
		uint ass_id = -1;
		vector<unique_ptr<Ref>> refs;
	};

	Shortcut() = default;
	Shortcut(Step* pr, Substitution&& s, const vector<Writable*>& hs = vector<Writable*>()) : hyps(hs), prop(pr), sub(std::move(s)) { }
	Shortcut(Shortcut&&) = default;
	vector<Writable*> hyps;
	Step* prop = nullptr;
	Substitution sub;
	Longcut longcut;

	int gain(const Assertion* ass) const {
		vector<const Writable*> children;
		for (auto w : hyps) {
			children.push_back(w);
		}
		set<const Writable*> inter = intermediate(prop, children);
		return inter.size() - (hyps.size() + 1);
	}
	void apply(const Assertion* ass) {
		longcut.ass_id = prop->ass_id();
		longcut.refs = std::move(prop->refs);
		prop->set_ass(ass->id());
		for (auto w : hyps) {
			prop->refs.emplace_back(make_unique<Ref>(w));
		}
	}
	void restore() {
		prop->set_ass(longcut.ass_id);
		prop->refs = std::move(longcut.refs);
	}

	string show() const {
		ostringstream oss;
		for (auto h : hyps) {
			oss << *h;
		}
		oss << "------------" << endl;
		oss << *prop << endl;
		oss << "subst:" << endl;
		oss << Indent::paragraph(sub.show());
		return oss.str();
	}
	string showIntermediate() const {
		ostringstream oss;
		vector<const Writable*> children;
		for (auto w : hyps) {
			children.push_back(w);
		}
		set<const Writable*> inter = intermediate(prop, children);
		vector<const Writable*> inter_vect;
		for (auto w : inter) {
			inter_vect.push_back(w);
		}
		std::sort(inter_vect.begin(), inter_vect.end(), [](const Writable* w1, const Writable* w2) {
			return Ref(const_cast<Writable*>(w1)) < Ref(const_cast<Writable*>(w2));
		});
		for (auto w : inter_vect) {
			oss << *w;
		}
		return oss.str();
	}
};

struct UnifPair {
	UnifPair(HypIndex::Unified&& u, Writable* n) : unif(std::move(u)), node(n) { }
	UnifPair(const HypIndex::Unified& u, Writable* n) : unif(u), node(n) { }
	HypIndex::Unified unif;
	Writable* node;
};

int child_ind(const Step* s, const Writable* ch) {
	uint ch_ind = -1;
	for (uint i = 0; i < s->refs.size(); ++ i) {
		auto& r = s->refs.at(i);
		if (r->step() == ch || r->hyp() == ch) {
			ch_ind = i;
			break;
		}
	}
	return ch_ind;
};

map<const Assertion*, Shortcut> find_proof_shortcuts(Proof* proof, const PropIndex& propIndex, const HypIndex& hypIndex) {
	map<Ref, vector<PropIndex::Unified>> props;
	map<Ref, map<const Assertion*, vector<HypIndex::Unified>>> hyps;
	map<const Assertion*, Shortcut> shortcuts;
	Watchdog watchdog(1000, "reduce shortcuts in " + Lex::toStr(proof->theorem->id()));
	try {
		traverseProof(proof->qed->step, [proof, &props, &hyps, &propIndex, &hypIndex, &watchdog](Writable* n) {
			if (Step* step = dynamic_cast<Step*>(n)) {
				prover::Term expr = prover::Tree2Term(
					*step->expr.tree(),
					prover::ReplMode::DENY_REPL,
					prover::LightSymbol::MATH_INDEX
				);
				for (PropIndex::Unified& unif : propIndex.unify(expr)) {
					Assertion* ass = unif.data->ass;
					if (!ass->token.preceeds(proof->theorem->token)) {
						continue;
					}
					if (ass == proof->theorem) {
						cout << "A proof cannot refer to itself" << endl;
						cout << ass->token.preceeds(proof->theorem->token) << endl;
						cout << ass->token.show() <<  endl;
						cout << ass->token.locate().show() <<  endl << "--------" << endl;
						cout << proof->theorem->token.show() <<  endl;
						cout << proof->theorem->token.locate().show() <<  endl;
						throw Error("A proof cannot refer to itself");
					}
					props[Ref(step)].emplace_back(std::move(unif));
				}
				map<const Assertion*, vector<HypIndex::Unified>> hypsMap;
				for (HypIndex::Unified& unif : hypIndex.unify(expr)) {
					Assertion* ass = unif.data->ass;
					if (!ass->token.preceeds(proof->theorem->token)) {
						continue;
					}
					if (ass == proof->theorem) {
						cout << "A proof cannot refer to itself" << endl;
						throw Error("A proof cannot refer to itself");
					}
					hypsMap[ass].emplace_back(std::move(unif));
				}
				hyps.emplace(Ref(step), std::move(hypsMap));
				watchdog.check();
			} else if (Hyp* hyp = dynamic_cast<Hyp*>(n)) {
				prover::Term expr = prover::Tree2Term(
					*hyp->expr.tree(),
					prover::ReplMode::DENY_REPL,
					prover::LightSymbol::MATH_INDEX
				);
				for (PropIndex::Unified& unif : propIndex.unify(expr)) {
					Assertion* ass = unif.data->ass;
					if (!ass->token.preceeds(proof->theorem->token)) {
						continue;
					}
					if (ass == proof->theorem) {
						cout << "A proof cannot refer to itself" << endl;
						throw Error("A proof cannot refer to itself");
					}
					props[Ref(hyp)].emplace_back(std::move(unif));
				}
				map<const Assertion*, vector<HypIndex::Unified>> hypsMap;
				for (HypIndex::Unified& unif : hypIndex.unify(expr)) {
					Assertion* ass = unif.data->ass;
					if (!ass->token.preceeds(proof->theorem->token)) {
						continue;
					}
					if (ass == proof->theorem) {
						cout << "A proof cannot refer to itself" << endl;
						throw Error("A proof cannot refer to itself");
					}
					hypsMap[ass].emplace_back(std::move(unif));
				}
				hyps.emplace(Ref(hyp), std::move(hypsMap));
				watchdog.check();
			} else {
				throw Error("must be a Step or Hyp");
			}
		});
		traverseProof(proof->qed->step, [&props, &hyps, &shortcuts, &watchdog](Writable* n) {
			watchdog.check();
			if (Step* step = dynamic_cast<Step*>(n)) {
				for (PropIndex::Unified& prop_unif : props.at(Ref(step))) {
					if (prop_unif.data->ass == step->ass()) {
						continue;
					}
					if (prop_unif.data->ass->hyps.size()) {
						vector<vector<UnifPair>> matched_hyps(prop_unif.data->ass->hyps.size());
						traverseProof(step, [step, &hyps, &matched_hyps, &prop_unif, &watchdog](Writable* m) {
							watchdog.check();
							if (Step* s = dynamic_cast<Step*>(m)) {
								if (s != step) {
									if (hyps.at(Ref(s)).count(prop_unif.data->ass)) {
										for (HypIndex::Unified& hyp_unif : hyps.at(Ref(s)).at(prop_unif.data->ass)) {
											if (prop_unif.sub.joinable(hyp_unif.sub)) {
												matched_hyps[hyp_unif.data->ind].push_back(UnifPair(hyp_unif, s));
											}
										}
									}
								}
							} else if (Hyp* h = dynamic_cast<Hyp*>(m)) {
								if (hyps.at(Ref(h)).count(prop_unif.data->ass)) {
									for (HypIndex::Unified& hyp_unif : hyps.at(Ref(h)).at(prop_unif.data->ass)) {
										if (prop_unif.sub.joinable(hyp_unif.sub)) {
											matched_hyps[hyp_unif.data->ind].push_back(UnifPair(hyp_unif, h));
										}
									}
								}
							} else {
								throw Error("must be a Step or Hyp");
							}
						});
						prover::CartesianProd<UnifPair> variants;
						for (auto& hyp_vect : matched_hyps) {
							variants.addDim(hyp_vect);
						}
						if (variants.card()) {
							if (variants.card() > 1024 * 32) {
								cout << "variants.card() = " << variants.card() << endl;
							}
							while (true) {
								watchdog.check();
								Assertion* ass = prop_unif.data->ass;
								Substitution sub = Subst2Substitution(prop_unif.sub);
								for (const Var* v : prop_unif.data->get()->expr.vars()) {
									if (!sub.maps(v->lit())) {
										sub.join(*v, VarTree(*v));
									}
								}
								vector<UnifPair> variant = variants.data();
								vector<Writable*> hyps;
								for (UnifPair& up : variant) {
									Substitution s = Subst2Substitution(up.unif.sub);
									for (const Var* v : up.unif.data->get()->expr.vars()) {
										if (!s.maps(v->lit())) {
											s.join(*v, VarTree(*v));
										}
									}
									if (!sub.join(s)) {
										break;
									}
									hyps.push_back(up.node);
								}
								if (sub.ok()) {
									Shortcut shortcut(step, std::move(sub), hyps);
									if (shortcut.gain(ass) > 0) {
										try {
											//cout << "1) ass: " << Lex::toStr(prop_unif.data->ass->id()) << endl;
											//cout << "s:" << endl << Indent::paragraph(s.show()) << endl;
											//cout << "step->expr: " << step->expr << endl;
											//cout << "apply(s, ass->prop->expr): " << apply(s, ass->prop->expr) << endl;
											ass->disj.check(shortcut.sub);
											//cout << "passed" << endl;
											shortcuts.emplace(ass, std::move(shortcut));
										} catch (Error& err) {
											//cout << err.msg << endl;
										}
									}
								}
								if (!variants.hasNext()) {
									break;
								} else {
									variants.makeNext();
								}
							}
						}
					} else {
						Shortcut shortcut(step, std::move(Subst2Substitution(prop_unif.sub)));
						if (shortcut.gain(prop_unif.data->ass) > 0) {
							try {
								//cout << "2) ass: " << Lex::toStr(prop_unif.data->ass->id()) << endl;
								//cout << "s:" << endl << Indent::paragraph(s.show()) << endl;
								prop_unif.data->ass->disj.check(shortcut.sub);
								//cout << "passed" << endl;
								shortcuts.emplace(prop_unif.data->ass, std::move(shortcut));
							} catch (Error& err) {
								//cout << err.msg << endl;
							}
						}
					}
				}
			}
		});
	} catch (Timeout& timeout) {
		cout << timeout.what() << endl;
	}
	return shortcuts;
}
void reduce_proof_shortcuts(Proof* proof, const PropIndex& propIndex, const HypIndex& hypIndex) {
	//cout << "to find shortcuts in: " << Lex::toStr(proof->theorem->id()) << " ...." << endl;
	map<const Assertion*, Shortcut> shortcuts = std::move(find_proof_shortcuts(proof, propIndex, hypIndex));
	if (!shortcuts.empty()) {
		cout << "shortcuts in: " << Lex::toStr(proof->theorem->id()) << endl;
		for (auto& p : shortcuts) {
			const Assertion* ass = p.first;
			Shortcut& shortcut = p.second;
			if (shortcut.gain(ass) > 0) {
				//ass->disj.check(shortcut.sub);
				cout << "\tfor assertion: " << Lex::toStr(ass->id()) << ", gain: " << shortcut.gain(ass) << endl;
				//cout << shortcut.show() << endl;
				//cout << shortcut.showIntermediate() << endl;
				//cout << endl << endl << endl;
				shortcut.apply(ass);
				Disj disj;
				proof->verify(VERIFY_SRC, &disj);
				if (!(disj <= proof->theorem->disj)) {
					cout << "RESTORED" << endl;
					shortcut.restore();
				}
			}
		}
	}
	//cout << *proof->theorem << endl;
	try {
		proof->verify();
	} catch (Error& err) {
		err.msg += "shortcuts in: " + Lex::toStr(proof->theorem->id()) + to_string(shortcuts.size()) + "\n";
		for (auto& p : shortcuts) {
			const Assertion* ass = p.first;
			Shortcut& shortcut = p.second;
			if (shortcut.gain(ass) > 0) {
				try {
					//ass->disj.check(shortcut.sub);
					err.msg += "\tfor assertion: " + Lex::toStr(ass->id()) + ", gain: " + to_string(shortcut.gain(ass)) + "\n";
					err.msg += shortcut.show() + "\n";
					err.msg += shortcut.showIntermediate() + "\n\n\n";
				} catch (Error&) {
					//cout << err.msg << endl;
				}
			}
		}
		err.msg += "of theorem:\n" + proof->theorem->show() + "\n";
		throw err;
	}
}

}

#ifdef PARALLEL
#define PARALLEL_REDUCE_PROOF_SHORTCUTS
#endif

void reduce_proof_shortcuts(const string& opts)  {
	auto parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	vector<Proof*> proofs;
	PropIndex propIndex;
	HypIndex hypIndex;
	for (auto& a : Sys::mod().math.get<Assertion>()) {
		Assertion* ass = a.second.data;
		if (Theorem* thm = dynamic_cast<Theorem*>(ass)) {
			if (Proof* proof = thm->proof.get()) {
				if (theorem == -1 || thm->id() == theorem) {
					proofs.push_back(proof);
				}
			}
		}
		propIndex.add(
			prover::Tree2Term(*ass->prop->expr.tree(), prover::ReplMode::KEEP_REPL, prover::LightSymbol::MATH_INDEX),
			PropRef(ass)
		);
		for (uint i = 0; i < ass->hyps.size(); ++i) {
			hypIndex.add(
				prover::Tree2Term(*ass->hyps.at(i)->expr.tree(), prover::ReplMode::KEEP_REPL, prover::LightSymbol::MATH_INDEX),
				HypRef(ass, i)
			);
		}
	}
	propIndex.init();
	hypIndex.init();
#ifdef PARALLEL_REDUCE_PROOF_SHORTCUTS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[&proofs, &propIndex, &hypIndex] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_proof_shortcuts(proofs[i], propIndex, hypIndex);
			}
		}
	);
#else
	for (auto proof : proofs) {
		reduce_proof_shortcuts(proof, propIndex, hypIndex);
	}
#endif
}

}} // mdl::rus

