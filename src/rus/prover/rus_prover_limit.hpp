#pragma once

#include <cmath>
#include <algorithm>
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct ProofsSizeLimit {
	struct PremiseDescr {
		PremiseDescr(uint i, uint s, uint h, bool f, const vector<uint>& a) : ind(i), size(s), hint(h), fixed(f), all(a) { }
		string show() const {
			ostringstream oss;
			oss << "Premise: " << ind << ", ";
			oss << "size: " << size << ", ";
			oss << "hint: " << (hint == -1 ? "-" : to_string(hint))<< ", ";
			oss << "fixed: " << (fixed ? "Y" : "N") << ", ";
			oss << "chosen size: " << chosen.size() << " {";
			for (uint i = 0; i < std::min(chosen.size(), static_cast<size_t>(30)); ++i) {
				oss << chosen[i] << ", ";
			}
			oss << "}, ";
			oss << "all size: " << all.size() << " {";
			for (uint i = 0; i < std::min(all.size(), static_cast<size_t>(30)); ++i) {
				oss << all[i] << ", ";
			}
			oss << "}, ";
			return oss.str();
		}
		uint ind;
		uint size;
		uint hint;
		bool fixed;
		vector<uint> all;
		vector<uint> chosen;
	};
	ProofsSizeLimit(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs, uint limit) : cardLimit_(limit) {
		for (uint i = 0; i < pr->premises.size(); ++ i) {
			auto& x = pr->premises[i];
			if (!x->proofs.size()) {
				return;
			}
			if (x.get() != hy) {
				uint hint = -1;
				vector<uint> all;
				for (uint j = 0; j < x->proofs.size(); ++j) {
					if (x->proofs[j]->hint) {
						hint = j;
					}
					all.push_back(j);
				}
				descrVect_.emplace_back(i, x->proofs.size(), hint, false, all);
			} else {
				uint hint = -1;
				vector<uint> all;
				for (uint j = 0; j < hs.size(); ++j) {
					if (hs[j].proof->hint) {
						hint = j;
					}
					all.push_back(hs[j].ind);
				}
				hypInd_ = i;
				descrVect_.emplace_back(i, hs.size(), hint, true, all);
			}
		}
		empty_ = false;
		chooseUniform();
	}
	uint cardTotal() const {
		uint c = 1;
		for (auto& d : descrVect_) {
			c *= d.size;
		}
		return c;
	}
	uint cardChosen() const {
		uint c = 1;
		for (auto& d : descrVect_) {
			c *= d.chosen.size();
		}
		return c;
	}
	uint cardLimit() const { return cardLimit_; }
	uint hypInd() const { return hypInd_; }

	string show() const {
		ostringstream oss;
		oss << "Proof size limits:" << endl;
		for (const auto& d : descrVect_) {
			oss << "\t" << d.show() << endl;
		}
		oss << "card total: " << cardTotal() << endl;
		oss << "card chosen: " << cardChosen() << endl;
		oss << "card limit: " << cardLimit() << endl;
		oss << "factor: " << factor_ << endl;
		return oss.str();
	}

	const vector<PremiseDescr>& descrVect() const { return descrVect_; }
	bool empty() const { return empty_; }

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
				for (auto& d : descrVect_) {
					uint i = 0;
					d.chosen.resize(d.size);
					std::generate_n(d.chosen.begin(), d.size, [&i]() { return i++; });
				}
			} else {
				factor_ = exp(log(static_cast<double>(cardLimit_) / total_card) / descrVect_.size());
				for (auto& d : descrVect_) {
					if (d.hint != -1) {
						d.chosen.push_back(d.hint);
					}
					uint chosen_card = static_cast<double>(d.size) * factor_;
					if (chosen_card == 0) {
						chosen_card = 1;
					}
					for (uint i = 0; i < ((d.hint != -1) ? chosen_card - 1 : chosen_card); ++ i) {
						uint ind = chooser(i, chosen_card, d.size);
						if (ind >= d.size) {
							throw Error("index overflow: " + to_string(ind) + " >= " + to_string(d.size));
						}
						d.chosen.push_back(ind);
					}
				}
			}
		}
	}
	uint cardLimit_;
	uint hypInd_ = -1;
	bool empty_ = true;
	double factor_ = 1;
	vector<PremiseDescr> descrVect_;
};

}}}

