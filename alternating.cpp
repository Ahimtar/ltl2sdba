/*
    Copyright (c) 2016 Juraj Major

    This file is part of LTL3TELA.

    LTL3TELA is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    LTL3TELA is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with LTL3TELA.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "utils.hpp"
#include "alternating.hpp"

bool is_mergeable(VWAA* vwaa, spot::formula f) {
	if (!f.is(spot::op::U)) {
		throw "Argument of is_mergeable is not an U-formula";
	}

	// we are not interested in cases where we save nothing
	if (f[1].is_boolean()) {
		return false;
	}

	// left argument has to be a state formula
	if (!f[0].is_boolean()) {
		return false;
	}

	// bdd of the left argument
	auto alpha = spot::formula_to_bdd(f[0], vwaa->spot_bdd_dict, vwaa->spot_aut);
	bool at_least_one_loop = false;
	// for each conjunction in DNF of psi test whether loops are covered by alpha
	for (auto& clause : f_bar(f[1])) {
		// convert a set of formulae into their conjunction
		auto sf = spot::formula::And(std::vector<spot::formula>(clause.begin(), clause.end()));
		// create the state for the conjunction
		unsigned state_id = make_alternating_recursive(vwaa, sf);
		// Check that any loop label impies alpha(f[0])
		for (auto& edge_id : vwaa->get_state_edges(state_id)) {
			auto t = vwaa->get_edge(edge_id);
			//check t is a loop
			auto tar_states = t->get_targets();
			std::set<spot::formula> targets;
			for (auto& tar_state : tar_states) {
				targets.insert(vwaa->state_name(tar_state));
			}
			if (std::includes(targets.begin(), targets.end(), clause.begin(), clause.end())) {
				// If label does not satisfy alpha, return false
				at_least_one_loop = true;
				if ((t->get_label() & alpha) != t->get_label()) {
					return false;
				}
			}
		}
	}

	if (o_mergeable_info && at_least_one_loop) {
		// only for experiments purposes
		std::cout << true << std::endl;
		std::exit(0);
	}

	return true;
}

void register_ap_from_boolean_formula(VWAA* slaa, spot::formula f) {
	// recursively register APs from a state formula f
	if (f.is(spot::op::And) || f.is(spot::op::Or)) {
		for (unsigned i = 0, size = f.size(); i < size; ++i) {
			register_ap_from_boolean_formula(slaa, f[i]);
		}
	} else {
		slaa->spot_aut->register_ap((f.is(spot::op::Not) ? spot::formula::Not(f) : f).ap_name());
	}
}

unsigned make_alternating_recursive(VWAA* slaa, spot::formula f) {
	if (slaa->state_exists(f)) {
		// we already have a state for f
		return slaa->get_state_id(f);
	} else {
		// create a new state
		unsigned state_id = slaa->get_state_id(f);

		if (f.is_tt()) {
			slaa->add_edge(state_id, bdd_true(), std::set<unsigned>());
		} else if (f.is_ff()) {
			// NOP
		} else if (f.is_boolean()) {
			// register APs in f
			register_ap_from_boolean_formula(slaa, f);

			// add the only edge to nowhere
			slaa->add_edge(state_id, spot::formula_to_bdd(f, slaa->spot_bdd_dict, slaa->spot_aut), std::set<unsigned>());
		} else if (f.is(spot::op::And)) {
			std::set<std::set<unsigned>> conj_edges;
			// create a state for each conjunct
			for (unsigned i = 0, size = f.size(); i < size; ++i) {
				conj_edges.insert(slaa->get_state_edges(make_alternating_recursive(slaa, f[i])));
			}
			// and add the product edges
			auto product = slaa->product(conj_edges, true);
			for (auto& edge : product) {
				slaa->add_edge(state_id, edge);
			}
		} else if (f.is(spot::op::Or)) {
			// create a state for each disjunct
			for (unsigned i = 0, size = f.size(); i < size; ++i) {
				auto fi_state_edges = slaa->get_state_edges(make_alternating_recursive(slaa, f[i]));
				// and add all its edges
				for (auto& edge : fi_state_edges) {
					slaa->add_edge(state_id, edge);
				}
			}
		} else if (f.is(spot::op::X)) {
			if (o_x_single_succ) {
				// translate X φ as (X φ) --tt--> (φ)
				std::set<unsigned> target_set = { make_alternating_recursive(slaa, f[0]) };
				slaa->add_edge(state_id, bdd_true(), target_set);
			} else {
				// we add an universal edge to all states in each disjunct
				auto f_dnf = f_bar(f[0]);

				for (auto& g_set : f_dnf) {
					std::set<unsigned> target_set;
					for (auto& g : g_set) {
						target_set.insert(make_alternating_recursive(slaa, g));
					}
					slaa->add_edge(state_id, bdd_true(), target_set);
				}
			}

		} else if (f.is(spot::op::R)) {
			// we build automaton for f[0] even if we don't need it for G
			// however, it doesn't cost much if f[0] == ff
			// the advantage is that we don't break order of APs
			unsigned left = make_alternating_recursive(slaa, f[0]);
			unsigned right = make_alternating_recursive(slaa, f[1]);

			// using traditional construction until "end of construction"
            std::set<unsigned> left_edges = slaa->get_state_edges(left);
            std::set<unsigned> right_edges = slaa->get_state_edges(right);

            unsigned loop_id = slaa->create_edge(bdd_true());
            slaa->get_edge(loop_id)->add_target(state_id);

            // remember the mark-discarding product should be used
            for (auto& right_edge : right_edges) {
                for (auto& left_edge : left_edges) {
                    slaa->add_edge(state_id, slaa->edge_product(right_edge, left_edge, false));
                }
                slaa->add_edge(state_id, slaa->edge_product(right_edge, loop_id, false));
			}
            // "end of construction"
		} else if (f.is(spot::op::U)) {
			auto& ac = slaa->spot_aut->acc();
			slaa->acc[f].fin = ac.add_set(); // create a new mark
			slaa->acc[f].inf = -1U; // default value for Inf-mark, meaning the mark does not have a value

			unsigned left = make_alternating_recursive(slaa, f[0]);
			unsigned right = make_alternating_recursive(slaa, f[1]);


            //using traditional construction until "end of construction"
            std::set<unsigned> left_edges = slaa->get_state_edges(left);
            std::set<unsigned> right_edges = slaa->get_state_edges(right);

            unsigned loop_id = slaa->create_edge(bdd_true());
            slaa->get_edge(loop_id)->add_target(state_id);

            slaa->add_edge(state_id, right_edges);

            for (auto& left_edge : left_edges) {
                auto p = slaa->edge_product(left_edge, loop_id, true);
                // the only mark is the new Fin
                slaa->get_edge(p)->clear_marks();
                slaa->get_edge(p)->add_mark(slaa->acc[f].fin);
                slaa->add_edge(state_id, p);
            }
			// end of construction
		}

		return state_id;
	}
}

VWAA* make_alternating(spot::formula f) {
	VWAA* vwaa = new VWAA(f);

	if (o_single_init_state) {
		std::set<unsigned> init_set = { make_alternating_recursive(vwaa, f) };
		vwaa->add_init_set(init_set);
	} else {
		std::set<std::set<spot::formula>> f_dnf = f_bar(f);

		for (auto& g_set : f_dnf) {
			std::set<unsigned> init_set;
			for (auto& g : g_set) {
				unsigned init_state_id = make_alternating_recursive(vwaa, g);
				init_set.insert(init_state_id);
			}
			vwaa->add_init_set(init_set);
		}
	}

	vwaa->build_acc();

	return vwaa;
}
