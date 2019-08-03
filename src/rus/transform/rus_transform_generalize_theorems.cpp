#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_maker.hpp>

namespace mdl { namespace rus {

extern bool debug_match;

void generalize_theorems(Theorem* thm, std::atomic<int>& counter) {
	//cout << (i == -1 ? "" : to_string(i) + " ")  << "testing proof maker of " << show_id(p->theorem->id()) << " ... " << std::flush;
	try {
		thm->verify();
		//cout << "TO GENERALIZE" << endl;
		//cout << *thm << endl;
	} catch (Error& err) {
		err.msg += "at generalize_theorems: thm->verify();\n";
		throw err;
	}
	AbstProof abstProof = thm->proof->abst();
	auto gen_name = [thm](uint i) { return "gen_" + string(i == 0 ? "" : to_string(i) + "_") + Lex::toStr(thm->id()); };
	uint i = 0;
	while (Sys::get().math.get<Assertion>().has(Lex::toInt(gen_name(i)))) {
		++i;
	}
	unique_ptr<Theorem> gen_thm = prover::make_theorem(abstProof, Lex::toInt(gen_name(i)));
	if (!gen_thm) {
		string err;
		err += "theorem " + Lex::toStr(thm->id()) + " couldn't be generalized\n";
		err += thm->show() + "\n";
		throw Error(err);
	}
	try {
		//cout << "GENERALIZED" << endl;
		//cout << *gen_thm << endl;
		try {
			beautify(*gen_thm);
		} catch (Error& err) {
			err.msg += "at generalize_theorems: beautify(*gen_thm);\n";
			throw err;
		}
		/*try {
			gen_thm->verify();
			//cout << "GENERALIZED" << endl;
			//cout << *gen_thm << endl;
		} catch (Error& err) {
			err.msg += "at generalize_theorems: gen_thm->veryfy();;\n";
			throw err;
		}*/
		vector<Substitution> matches1 = match(*gen_thm, *thm);
		if (!matches1.size()) {

			debug_match = true;
			match(*gen_thm, *thm);
			debug_match = false;
			string err;
			err += "remaked proof is less general then the original\n";
			err += "remaked theorem:\n" + gen_thm->show() + "\n";
			err += "original theorem:\n" + thm->show() + "\n";
			cout << err;
			throw Error(err);
		}
		vector<Substitution> matches2 = match(*thm, *gen_thm);
		if (!matches2.size()) {
			gen_thm->token = thm->token;
			Source* src = Sys::mod().math.get<Source>().access(thm->token.src()->id());
			uint pos = -1;
			for (uint i = 0; i < src->theory.nodes.size(); ++i) {
				const Theory::Node& n = src->theory.nodes.at(i);
				const Writable* w = Theory::get(n);
				if (const WithToken* t = dynamic_cast<const WithToken*>(w)) {
					if (t->token == thm->token) {
						pos = i;
						break;
					}
				}

			}

			cout << "theorem " << Lex::toStr(thm->id()) << " is generalized" << endl;
			//cout << "more general:\n" << gen_thm->show() << endl;
			//cout << "original:\n" << thm->show() << endl;
			if (pos == -1) {
				throw Error("theorem " + Lex::toStr(thm->id()) + " couldn't be located");
			}
			src->theory.insert(gen_thm.release(), pos);

			counter.store(counter.load() + 1);
		}
	} catch (Timeout& timeout) {
		cout << timeout.what();
	} catch (Error& err) {
		err.msg += "at generalize_theorems: " + Lex::toStr(thm->id()) + "\n";
		throw err;
	}
}

#ifdef PARALLEL
#define PARALLEL_GENERALIZE_THEOREMS
#endif

void generalize_theorems(const string& opts)  {
	map<string, string> parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	std::atomic<int> counter(0);
	vector<Theorem*> theorems;
	for (Assertion& a : Sys::mod().math.get<Assertion>()) {
		if (Theorem* thm = dynamic_cast<Theorem*>(&a)) {
			if (thm->proof) {
				if (theorem == -1 || thm->id() == theorem) {
					theorems.push_back(thm);
				}
			}
		}
	}
#ifdef PARALLEL_GENERALIZE_THEOREMS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, theorems.size()),
		[&theorems, &counter] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				generalize_theorems(theorems[i], counter);
			}
		}
	);
#else
	for (auto th : theorems) {
		generalize_theorems(th, counter);
	}
#endif
	if (counter.load() > 0) {
		cout << "totally generalized theorems: " << counter.load() << endl;
	}
}

}} // mdl::rus
