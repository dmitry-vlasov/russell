#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus {

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
			const vector<uint>* previous = expressions.findTerm(term);
			if (previous && previous->size()) {
				steps_map[step] = new_steps.at(previous->at(0));
			} else {
				uint new_ind = new_steps.size();
				Step* new_step = new Step(
					new_ind, step->kind(), step->ass_id(), step->proof_, step->token
				);
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
			new_elems.push_back(std::move(e)); break;
		}
		case Proof::VARS: {
			new_elems.push_back(std::move(e)); break;
		}
		}
	}
	if (new_elems.size() < proof->elems.size()) {
		cout << "diff: " << (proof->elems.size() - new_elems.size()) << ", new_elems.size() = " << new_elems.size() << " < " << proof->elems.size() << " = proof->elems.size()" << endl;
		proof->elems = std::move(new_elems);
	}
}

void reduce_duplcate_steps()  {
	for (auto& p : Sys::mod().math.get<Proof>()) {
		if (Proof* proof = p.second.data) {
			reduce_duplcate_steps(proof);
		}
	}
}

}} // mdl::rus
