#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_cartesian.hpp>

namespace mdl { namespace rus {

extern bool debug_check_disj;

namespace {

struct StepRef {
	StepRef(uint i, Substitution&& s) : ind(i), sub(s) { }
	uint ind;
	Substitution sub;
};

void replace_with_optimal(Proof* proof) {
	Disj theorem_disj = unite(proof->theorem->disj, proof->disj);
	for (auto& s : proof->steps) {
		Step* step = s.get();
		if (step->ass()->info && step->ass()->info->optimal != step->ass()->id()) {
			const Assertion* optimal = Sys::get().math.get<Assertion>().access(step->ass()->info->optimal);
			if (optimal->token.preceeds(proof->theorem->token)) {
				prover::CartesianProd<StepRef> vars;
				for (uint i = 0; i < optimal->hyps.size(); ++ i) {
					vector<StepRef> dimData;
					const Expr& hyp = optimal->hyps.at(i)->expr;
					for (uint j = 0; j < step->refs.size(); ++ j) {
						const Expr& ref = step->refs.at(j)->expr();
						Substitution s = std::move(unify_forth(hyp, ref));
						if (s.ok()) {
							dimData.emplace_back(j, std::move(s));
						}
					}
					vars.addDim(dimData);
				}
				if (!vars.card()) {
					throw Error("must not be empty");
				}
				Substitution sub = std::move(unify_forth(optimal->prop->expr, step->expr));
				while (true) {
					const vector<StepRef>& var = vars.data();
					Substitution s(sub);
					for (uint i = 0; i < optimal->hyps.size(); ++ i) {
						if (!s.join(var.at(i).sub)) {
							break;
						}
					}

					/*if ((step->ass()->id() == Lex::toInt("elab2") && optimal->id() == Lex::toInt("gen_elab2")) ||
						(step->ass()->id() == Lex::toInt("nfcri") && optimal->id() == Lex::toInt("nfel2"))) {
						cout << "Assertion " << Lex::toStr(step->ass()->id()) << " SHOULD BE replaced with ";
						cout << Lex::toStr(optimal->id()) << " in step " << step->ind();
						cout << " of proof of " << Lex::toStr(proof->theorem->id()) << endl;
						cout << "sub: " << endl;
						cout << s << endl;
						cout << "optimal:" << endl;
						cout << *optimal << endl;
						cout << "ass:" << endl;
						cout << *step->ass() << endl;
						cout << "theorem:" << endl;
						cout << *step->proof()->theorem << endl;
						cout << "optimal->disj.satisfies(s, theorem_disj): " << optimal->disj.satisfies(s, theorem_disj) << endl;
						debug_check_disj = true;
						optimal->disj.satisfies(s, step->ass()->disj);
						debug_check_disj = false;
					}*/

					if (s.ok() && optimal->disj.satisfies(s, &theorem_disj)) {
						cout << "Assertion " << Lex::toStr(step->ass()->id()) << " replaced with ";
						cout << Lex::toStr(optimal->id()) << " in step " << step->ind();
						cout << " of proof of " << Lex::toStr(proof->theorem->id()) << endl;
						step->set_ass(optimal->id());
						vector<unique_ptr<Ref>> new_refs;
						for (uint i = 0; i < optimal->hyps.size(); ++ i) {
							int j = var.at(i).ind;
							new_refs.emplace_back(make_unique<Ref>(*step->refs.at(j)));
						}
						step->refs = std::move(new_refs);
						return;
					}
					if (vars.hasNext()) {
						vars.makeNext();
					} else {
						break;
					}
				}
				string err = "must unify somehow\n";
				err += "Assertion " + Lex::toStr(step->ass()->id()) + " must be replaced with ";
				err += Lex::toStr(optimal->id()) + " in step " + to_string(step->ind());
				err += " of proof of " + Lex::toStr(proof->theorem->id()) + "\n";
				err += step->show() + "\n";
				err += step->ass()->show() + "\n";
				err += optimal->show() + "\n";
				throw Error(err);
			}
		}
	}
	proof->theorem->verify(VERIFY_SRC);
}

}

#ifdef PARALLEL
#define PARALLEL_REPLACE_WITH_OPTIMAL_SHORTCUTS
#endif

void replace_with_optimal(const string& opts)  {
	map<string, string> parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	vector<Proof*> proofs;
	for (Assertion& ass : Sys::mod().math.get<Assertion>()) {
		if (Theorem* thm = dynamic_cast<Theorem*>(&ass)) {
			if (Proof* proof = thm->proof.get()) {
				if (theorem == -1 || thm->id() == theorem) {
					proofs.push_back(proof);
				}
			}
		}
	}
#ifdef PARALLEL_REPLACE_WITH_OPTIMAL_SHORTCUTS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[&proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				replace_with_optimal(proofs[i]);
			}
		}
	);
#else
	for (auto proof : proofs) {
		replace_with_optimal(proof);
	}
#endif
}

}} // mdl::rus

