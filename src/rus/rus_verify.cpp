#include <rus_ast.hpp>

namespace mdl { namespace rus {

bool debug_verify = false;

void Step::verify(uint mode, Disj* disj) const {
	if (kind() == Step::CLAIM) {
		claim()->verify(mode);
		return;
	}
	if (mode & VERIFY_SUB) {
		assert(kind() == Step::ASS);

		//if (debug_verify) {
		//	cout << "unifying step: " << *this << endl;
		//}

		if (!ass()) throw Error("unknown assertion", Lex::toStr(ass_id()));
		sub = unify_forth(ass()->prop->expr, expr);
		if (!sub) {
			string msg = "proposition:\n";
			msg += ass()->prop->show() + "\n";
			msg += "ref expr:\n";
			msg += ass()->prop->expr.show() + "\n";
			msg += "step:\n";
			msg += show() + "\n";
			msg += expr.show() + "\n\n";
			if (proof()->theorem) {
				msg += "theorem " + Lex::toStr(proof()->theorem->id()) + "\n";
			}
			throw Error("proposition unification failed", msg);
		}
		if (ass()->arity() != refs.size()) {
			string msg = "proposition:\n";
			msg += ass()->prop->show() + "\n";
			msg += "refs size: " + to_string(refs.size()) + " != " + to_string(ass()->arity()) + "\n";
			msg += "step:\n";
			msg += show() + "\n";
			if (proof()->theorem) {
				msg += "theorem " + Lex::toStr(proof()->theorem->id()) + "\n";
			}
			throw Error("proposition unification failed", msg);
		}
		//if (debug_verify) {
		//	cout << "sub_0: " << endl << sub;
		//	cout << ass()->prop->expr << " -- " << expr << endl << endl;
		//}
		for (uint i = 0; i < ass()->arity(); ++ i) {
			/*if (debug_verify && proof()->theorem->id() == Lex::toInt("euind")) {
				cout << "TO UNIFY:" << endl;
				cout << "step: " << ind_ << endl;
				cout << "theorem: " << Lex::toStr(proof()->theorem->id()) << " -- " << i << endl;
				cout << Lex::toStr(ass()->id()) << " -- " << i << endl;
				cout << ass()->hyps.at(i)->expr << flush;
				cout << " -- " << refs.at(i)->expr() << endl << endl;
			}*/

			Substitution hs = unify_forth(ass()->hyps.at(i)->expr, refs.at(i)->expr());
			if (!hs) {
				string msg = "\nhypothesis:\n";
				msg += ass()->hyps.at(i)->show() + "\n";
				msg += "ref expr:\n";
				msg += refs.at(i)->expr().show() + "\n\n";
				msg += "step:\n";
				msg += show() + "\n\n";
				if (proof()->theorem) {
					msg += "theorem " + Lex::toStr(proof()->theorem->id()) + "\n";
				}
				msg += "substitution:\n" + sub.show() + "\n";
				throw Error("hypothesis unification failed", msg);
			}
			//if (!sub.join(const_cast<const Substitution&>(hs))) {
			if (!sub.join(hs)) {
				string msg = "\nhypothesis:\n";
				msg += ass()->hyps.at(i)->show() + "\n";
				msg += "ref expr:\n";
				msg += refs.at(i)->expr().show() + "\n\n";
				msg += "step:\n";
				msg += show() + "\n\n";
				if (proof()->theorem) {
					msg += "theorem " + Lex::toStr(proof()->theorem->id()) + "\n";
				}
				msg += "prop substitution:\n" + sub.show() + "\n";
				msg += "hyp substitution:\n" + hs.show() + "\n";
				throw Error("substitution join failed", msg);
			}
			//if (debug_verify) {
			//	cout << "hs: " << endl << hs << endl;
			//	cout << "sub_" << (i + 1) << ": " << endl << sub;
			//	cout << ass()->hyps.at(i)->expr << " -- " << refs.at(i)->expr() << endl << endl;
			//}
		}
		/*if (debug_verify) {
			//cout << "unifying step: " << *this << endl;
			//cout << "ass: " << *ass() << endl;
			//cout << "sub: " << endl << sub << endl;
			cout << "hyps: " << endl;
			for (uint i = 0; i < ass()->arity(); ++ i) {
				cout << "\t" << apply(sub, ass()->hyps.at(i)->expr) << " ?= " << apply(sub, refs.at(i)->expr()) << endl;
			}
		}*/
	}
	if (mode & VERIFY_DISJ) {
		try {
			ass()->disj.check(sub, disj);
		} catch (Error& err) {
			//ostringstream oss;
			//ass()->disj.write(oss);
			//err.msg += "assertion: " + Lex::toStr(ass()->id()) + "\n";
			err.msg += "assertion:\n" + ass()->show() + "\n";
			//err.msg += "disjointeds: " + oss.str() + "\n";
			err.msg += "substitution:\n" + Indent::paragraph(sub.show()) + "\n";
			//err.msg += "step: " + to_string(ind_) + "\n";
			err.msg += "step: " + show() + "\n";
			//err.msg += "in proof of theorem: " + Lex::toStr(proof_->theorem->id()) + "\n";
			if (proof_->theorem) {
				err.msg += "theorem:\n" + proof_->theorem->show() + "\n";
			}
			throw err;
		}
	}
}

void Qed::verify(uint mode) const {
	if ((mode & VERIFY_QED) && (prop->expr != step->expr))
		throw Error("qed prop doesn't match qed step", prop->expr.show() + " != " + step->expr.show());
}

void Proof::verify(uint mode, Disj* disj) const {
	//cout << "PROOF OF " << Lex::toStr(theorem->id()) << endl;
	//if (theorem->id() == Lex::toInt("19.8w")) {
	//	cout << "RRRRR" << endl << *theorem << endl;
	//}
	for (const auto& step : steps) {
		step->verify(mode, disj);
	}
	if (qed) {
		qed->verify(mode);
	}
}

void Theorem::verify(uint mode) {
	if (proof) {
		if (mode & UPDATE_DISJ) {
			disj.dvars.clear();
			proof->disj.dvars.clear();
			Disj all_disj;
			proof->verify(mode, &all_disj);
			std::set<uint> theorem_vars = vars.vars();
			for (auto& p : all_disj.dvars) {
				if (theorem_vars.count(p.v) && theorem_vars.count(p.w)) {
					disj.dvars.insert(p);
				} else {
					proof->disj.dvars.insert(p);
				}
			}
		} else {
			proof->verify(mode);
		}
	} else {
		throw Error("Theorem has no proof", Lex::toStr(id()));
	}
}

bool Proof::check(uint mode) const {
	try {
		verify(mode);
		return true;
	} catch (Error&) {
		return false;
	}
}

void verify_theory(Theory* theory, uint mode) {
	for (auto& n : theory->nodes) {
		switch (Theory::kind(n)) {
		case Theory::THEORY:  verify_theory(Theory::theory(n), mode); break;
		case Theory::THEOREM: Theory::theorem(n)->verify(mode);       break;
		default: break;
		}
	}
}

void verify_source(uint src, uint mode, set<uint>& verified) {
	if (verified.count(src)) return;
	verified.insert(src);
	Source* source = Sys::mod().math.get<Source>().access(src);
	if (mode & VERIFY_DEEP) {
		for (auto& imp : source->imports) {
			verify_source(imp->source.id(), mode, verified);
		}
	}
	verify_theory(&source->theory, mode);
}

#ifdef PARALLEL
#define PARALLEL_VERIFY
#endif

void verify(uint src) {
	if (src == -1) {
		vector<const Proof*> proofs;
		for (const Assertion& a : Sys::get().math.get<Assertion>()) {
			if (const Theorem* t = dynamic_cast<const Theorem*>(&a)) {
				if (!t->proof) {
					throw Error("Theorem is not proved", show_id(t->id()));
				} else {
					proofs.push_back(t->proof.get());
				}
			}
		}
#ifdef PARALLEL_VERIFY
		tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
			[proofs] (const tbb::blocked_range<size_t>& r) {
				for (size_t i = r.begin(); i != r.end(); ++i)
					proofs.at(i)->verify(VERIFY_SUB | VERIFY_QED);
			}
		);
#else
	for (auto p : proofs) {
		p->verify(VERIFY_SUB | VERIFY_QED);
	}
#endif
		set<uint> verified;
		for (const Source& s : Sys::mod().math.get<Source>()) {
			verify_source(s.id(), VERIFY_DISJ | UPDATE_DISJ | VERIFY_DEEP, verified);
		}
	} else {
		set<uint> verified;
		verify_source(src, VERIFY_SUB | VERIFY_QED | VERIFY_DISJ | UPDATE_DISJ, verified);
	}
}

}} // mdl::rus
