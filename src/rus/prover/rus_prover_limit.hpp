#pragma once

#include <cmath>
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct ProofsSizeLimit {
	struct PremiseDescr {
		PremiseDescr(uint i, uint s, uint h, bool f) : ind(i), size(s), hint(h), fixed(f) { }
		string show() const {
			ostringstream oss;
			oss << "Premise: " << ind << ", ";
			oss << "size: " << size << ", ";
			oss << "hint: " << (hint == -1 ? "-" : to_string(hint))<< ", ";
			oss << "fixed: " << (fixed ? "Y" : "N") << ", ";
			oss << "chosen size: " << chosen.size();
			return oss.str();
		}
		uint ind;
		uint size;
		uint hint;
		bool fixed;
		vector<uint> chosen;
	};
	ProofsSizeLimit(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs, uint limit) : cardLimit_(limit) {
		for (uint i = 0; i < pr->premises.size(); ++ i) {
			auto& x = pr->premises[i];
			if (x.get() != hy) {
				uint hint = -1;
				for (uint i = 0; i < x->proofs.size(); ++i) {
					if (x->proofs[i]->hint) {
						hint = i;
					}
				}
				descrVect.emplace_back(i, x->proofs.size(), hint, false);
			} else {
				uint hint = -1;
				for (uint i = 0; i < hs.size(); ++i) {
					if (hs[i].proof->hint) {
						hint = i;
					}
				}
				hypInd_ = i;
				descrVect.emplace_back(i, hs.size(), hint, true);
			}
		}
		chooseUniform();
	}
	uint cardTotal() const {
		uint c = 1;
		for (auto& d : descrVect) {
			c *= d.size;
		}
		return c;
	}
	uint cardChosen() const {
		uint c = 1;
		for (auto& d : descrVect) {
			c *= d.chosen.size();
		}
		return c;
	}
	uint cardLimit() const { return cardLimit_; }
	uint hypInd() const { return hypInd_; }

	string show() const {
		ostringstream oss;
		oss << "Proof size limits:" << endl;
		for (const auto& d : descrVect) {
			oss << "\t" << d.show() << endl;
		}
		oss << "card total: " << cardTotal() << endl;
		oss << "card chosen: " << cardChosen() << endl;
		oss << "card limit: " << cardLimit() << endl;
		return oss.str();
	}

	vector<PremiseDescr> descrVect;

private:
	void chooseUniform() {
		choose([](uint ind, uint chosen_card, uint total_card) {
			return ind * total_card / chosen_card;
		});
	}

	void chooseRandom() {
		choose([](uint ind, uint chosen_card, uint total_card) {
			return random() % total_card;
		});
	}

	void choose(function<uint (uint, uint, uint)> chooser) {
		uint total_card = cardTotal();
		if (total_card > 0) {
			if (total_card <= cardLimit_) {
				for (auto& d : descrVect) {
					uint i = 0;
					d.chosen.resize(d.size);
					std::generate_n(d.chosen.begin(), d.size, [&i]() { return i++; });
				}
			} else {
				double factor = exp(log(cardLimit_ / total_card) / descrVect.size());
				for (auto& d : descrVect) {
					d.chosen.push_back(d.hint);
					uint chosen_card = d.size * factor;
					for (uint i = 0; i < chosen_card - 1; ++ i) {
						d.chosen.push_back(chooser(i, chosen_card, d.size));
					}
				}
			}
		}
	}
	uint cardLimit_;
	uint hypInd_ = -1;
};

}}}

