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
	Shortcut() = default;
	Shortcut(Step* pr, prover::Subst&& s, const vector<Writable*>& hs = vector<Writable*>()) : hyps(hs), prop(pr), sub(std::move(s)) { }
	Shortcut(Shortcut&&) = default;
	vector<Writable*> hyps;
	Step* prop = nullptr;
	prover::Subst sub;

	int gain(const Assertion* ass) const {
		vector<const Writable*> children;
		for (auto w : hyps) {
			children.push_back(w);
		}
		set<const Writable*> inter = intermediate(prop, children);
		return inter.size() - (hyps.size() + 1);
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

void reduce_proof_shortcuts(Proof* proof, const PropIndex& propIndex, const HypIndex& hypIndex) {
	map<Ref, vector<PropIndex::Unified>> props;
	map<Ref, map<const Assertion*, vector<HypIndex::Unified>>> hyps;
	traverseProof(proof->qed->step, [proof, &props, &hyps, &propIndex, &hypIndex](Writable* n) {
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
				props[Ref(step)].emplace_back(std::move(unif));
			}
			map<const Assertion*, vector<HypIndex::Unified>> hypsMap;
			for (HypIndex::Unified& unif : hypIndex.unify(expr)) {
				Assertion* ass = unif.data->ass;
				if (!ass->token.preceeds(proof->theorem->token)) {
					continue;
				}
				/*if (ass->id() == Lex::toInt("mp1i") && step->ass()->id() == Lex::toInt("ioran")) {
					cout << "unif.sub: " << unif.data->ind << endl;
					cout << unif.sub << endl;
				}*/
				hypsMap[ass].emplace_back(std::move(unif));
			}
			hyps.emplace(Ref(step), std::move(hypsMap));
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
				props[Ref(hyp)].emplace_back(std::move(unif));
			}
			map<const Assertion*, vector<HypIndex::Unified>> hypsMap;
			for (HypIndex::Unified& unif : hypIndex.unify(expr)) {
				Assertion* ass = unif.data->ass;
				if (!ass->token.preceeds(proof->theorem->token)) {
					continue;
				}
				hypsMap[ass].emplace_back(std::move(unif));
			}
			hyps.emplace(Ref(hyp), std::move(hypsMap));
		} else {
			throw Error("must be a Step or Hyp");
		}
	});
	/*cout << "props" << endl;
	for (auto& p : props) {
		cout << p.first.show() << endl;
		cout << p.first.expr().show() << " --> {" << endl;
		for (auto& u : p.second) {
			cout << "\t[" << endl;
			cout << Indent::paragraph(Lex::toStr(u.data->ass->id()), 2) << endl;
			//cout << Indent::paragraph(u.data->ass->show(), 2) << endl;
			cout << Indent::paragraph(u.sub.show(), 2) << endl;
			cout << "\t], " << endl;

		}
		cout << "}" << endl;
	}*/
	/*cout << "hyps" << endl;
	for (auto& p : hyps) {
		if (p.first.step()->ass()->id() != Lex::toInt("ioran")) {
			continue;
		}
		cout << p.first.show() << endl;
		cout << p.first.expr().show() << " --> {" << endl;
		for (auto& q : p.second) {
			if (q.first->id() != Lex::toInt("mp1i")) {
				continue;
			}
			//cout << Indent::paragraph(q.first->show()) << " --> " << endl;
			cout << Indent::paragraph(Lex::toStr(q.first->id()), 2) << " --> " << endl;
			cout << "\t[" << endl;
			for (auto& u : q.second) {
				//cout << Indent::paragraph(u.data->ass->show(), 2) << endl;
				cout << Indent::paragraph(Lex::toStr(u.data->ass->id()), 2) << endl;
				cout << Indent::paragraph(u.sub.show(), 2) << endl;
			}
			cout << "\t], " << endl;

		}
		cout << "}" << endl;
	}*/

	/*traverseProof(proof->qed->step, [&props, &hyps](Writable* n) {
		if (Step* step = dynamic_cast<Step*>(n)) {
			bool found = false;
			for (auto& u : props.at(Ref(step))) {
				if (u.data->ass == step->ass()) {
					found = true;
					break;
				}
			}
			if (!found) {
				throw Error("ass not found");
			}
			for (uint i = 0; i < step->refs.size(); ++i) {
				auto& r = step->refs.at(i);
				if (Step* s = r->step()) {
					map<const Assertion*, vector<HypIndex::Unified>> m = hyps.at(Ref(s));
					if (!m.count(step->ass())) {
						throw Error("ass from step not found");
					}
					found = false;
					for (auto& u : m.at(step->ass())) {
						if (u.data->ass == step->ass() && u.data->ind == i) {
							found = true;
							break;
						}
					}
					if (!found) {
						throw Error("step not found");
					}
				} else if (Hyp* h = r->hyp()) {
					map<const Assertion*, vector<HypIndex::Unified>> m = hyps.at(Ref(h));
					if (!m.count(step->ass())) {
						throw Error("ass from hyp not found");
					}
					found = false;
					for (auto& u : m.at(step->ass())) {
						if (u.data->ass == step->ass() && u.data->ind == i) {
							found = true;
							break;
						}
					}
					if (!found) {
						throw Error("hyp not found");
					}
				}
			}

		} else if (Hyp* hyp = dynamic_cast<Hyp*>(n)) {

		}
	});*/

	map<const Assertion*, Shortcut> shortcuts;
	traverseProof(proof->qed->step, [&props, &hyps, &shortcuts](Writable* n) {
		if (Step* step = dynamic_cast<Step*>(n)) {
			for (PropIndex::Unified& prop_unif : props.at(Ref(step))) {
				if (prop_unif.data->ass == step->ass()) {
					continue;
				}
				if (prop_unif.data->ass->hyps.size()) {

					/*if (prop_unif.data->ass->id() == Lex::toInt("mp1i")) {
						cout << "traversing prop_unif... mp1i" << endl;
						cout << "sub:" << endl;
						cout << prop_unif.sub << endl;
						cout << "props size: " << props.at(Ref(step)).size() << endl;
					}*/

					vector<vector<UnifPair>> matched_hyps(prop_unif.data->ass->hyps.size());
					traverseProof(step, [step, &hyps, &matched_hyps, &prop_unif](Writable* m) {
						if (Step* s = dynamic_cast<Step*>(m)) {
							if (s != step) {

								//if (prop_unif.data->ass->id() == Lex::toInt("mp1i") && s->ass()->id() == Lex::toInt("ioran")) {
								//	cout << "traversing s... mp1i -- ioran" << endl;
								//}

								uint ch_ind = child_ind(step, s);
								if (hyps.at(Ref(s)).count(prop_unif.data->ass)) {
									bool ch_found = false;
									for (HypIndex::Unified& hyp_unif : hyps.at(Ref(s)).at(prop_unif.data->ass)) {

										/*if (prop_unif.data->ass->id() == Lex::toInt("mp1i") && s->ass()->id() == Lex::toInt("ioran")) {
											cout << "hyp_unif.sub: " << hyp_unif.data->ind << endl;
											cout << "hyps.size() = " << hyps.at(Ref(s)).at(prop_unif.data->ass).size() << endl;
											cout << hyp_unif.sub << endl;
										}*/

										ch_found = ch_found ||
											(hyp_unif.data->ass == prop_unif.data->ass &&
											hyp_unif.data->ass == step->ass() &&
											hyp_unif.data->ind == ch_ind );

										if (prop_unif.sub.joinable(hyp_unif.sub)) {



											matched_hyps[hyp_unif.data->ind].push_back(UnifPair(hyp_unif, s));
										} else {
											/*if (ch_found && ch_ind != -1 && prop_unif.data->ass == step->ass()) {
												string err("child step not unified\n");
												err += "prop_unif.sub:\n" + prop_unif.sub.show() + "\n";
												err += "hyp_unif.sub:\n" + hyp_unif.sub.show() + "\n\n";
												err += "prop_unif.data->ass: " + Lex::toStr(prop_unif.data->ass->id()) + "\n";
												err += "ch_ind: " + to_string(ch_ind) + "\n\n";
												err += "ass: " + prop_unif.data->ass->show() + "\n";
												throw Error(err);
											}*/
										}
									}
									if (!ch_found && ch_ind != -1 && prop_unif.data->ass == step->ass()) {
										string err("child step hyp not found\n");
										err += "prop_unif.data->ass: " + Lex::toStr(prop_unif.data->ass->id()) + "\n";
										err += "ch_ind: " + to_string(ch_ind) + "\n\n";
										for (HypIndex::Unified& hyp_unif : hyps.at(Ref(s)).at(prop_unif.data->ass)) {
											err += "hyp_unif.data->ass: " + Lex::toStr(hyp_unif.data->ass->id()) + "\n";
											err += "hyp_unif.data->ind: " + to_string(hyp_unif.data->ind) + "\n";
										}
										throw Error(err);
									}
								} else {
									if (ch_ind != -1 && prop_unif.data->ass == step->ass()) {
										throw Error("child step not found");
									}
								}
							}
						} else if (Hyp* h = dynamic_cast<Hyp*>(m)) {
							uint ch_ind = child_ind(step, h);
							if (hyps.at(Ref(h)).count(prop_unif.data->ass)) {
								for (HypIndex::Unified& hyp_unif : hyps.at(Ref(h)).at(prop_unif.data->ass)) {
									if (prop_unif.sub.joinable(hyp_unif.sub)) {
										matched_hyps[hyp_unif.data->ind].push_back(UnifPair(hyp_unif, h));
									}
								}
							} else {
								if (ch_ind != -1 && prop_unif.data->ass == step->ass()) {
									throw Error("child hyp not found");
								}
							}
						} else {
							throw Error("must be a Step or Hyp");
						}
					});
					prover::CartesianProd<UnifPair> variants;
					uint i = 0;
					for (auto& hyp_vect : matched_hyps) {
						//cout << "hyp_vect[" << i++ << "].size() " << hyp_vect.size() << endl;
						variants.addDim(hyp_vect);
					}
					if (variants.card()) {

						//cout << "variants.card() = " << variants.card() << endl;

						while (true) {
							Assertion* ass = prop_unif.data->ass;
							prover::Subst sub = prop_unif.sub;
							vector<UnifPair> variant = variants.data();
							vector<Writable*> hyps;
							for (UnifPair& up : variant) {

								/*if (ass->id() == Lex::toInt("mp1i") && step->ass()->id() == Lex::toInt("sylbi")) {
									cout << "up.unif.sub:" << endl;
									cout << up.unif.sub << endl;

								}*/

								if (!sub.join(up.unif.sub)) {
									break;
								}
								hyps.push_back(up.node);
							}
							if (sub.ok()) {
								Shortcut shortcut(step, std::move(sub), hyps);
								if (shortcut.gain(ass) > 0) {
									shortcuts.emplace(ass, std::move(shortcut));
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
					Shortcut shortcut(step, std::move(prop_unif.sub));
					if (shortcut.gain(prop_unif.data->ass) > 0) {
						shortcuts.emplace(prop_unif.data->ass, std::move(shortcut));
					}
				}
			}
		}
	});

	if (!shortcuts.empty()) {
		cout << "shortcuts in: " << Lex::toStr(proof->theorem->id()) << endl;
		for (auto& p : shortcuts) {
			cout << "shortcut found:" << endl;
			cout << p.second.show() << endl;
			cout << "for assertion: " << endl;
			cout << *p.first;
			cout << "gain: " << p.second.gain(p.first) << endl;
			cout << p.second.showIntermediate() << endl;
			/*cout << "raw hyps:" << endl;
			for (HypIndex::Unified& hyp_unif : hyps.at(Ref(s)).at(prop_unif.data->ass)) {

			}*/
			cout << endl << endl << endl;
		}
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
			prover::Tree2Term(*ass->prop->expr.tree(), prover::ReplMode::KEEP_REPL, prover::LightSymbol::ASSERTION_INDEX),
			PropRef(ass)
		);
		for (uint i = 0; i < ass->hyps.size(); ++i) {
			hypIndex.add(
				prover::Tree2Term(*ass->hyps.at(i)->expr.tree(), prover::ReplMode::KEEP_REPL, prover::LightSymbol::ASSERTION_INDEX),
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

