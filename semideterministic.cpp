/*
    Copyright (c) 2018 Michal Románek

    This file is part of LTL2SDBA.

    LTL2SDBA is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    LTL2SDBA is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with LTL2SDBA.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <cstring>
#include "semideterministic.hpp"

// These are all prefixed by "g" meaning "global" for clarity in code
std::vector<bdd> gAlphabet; // All the combinations of atomic propositions
unsigned gnc; // Number of states of non-deterministic part of SDBA
unsigned gnvwaa; // Number of states of the original VWAA
unsigned gtnum; // Number of the state t
unsigned gLabel;
bool gImplies;
// This is the only exception to remind that the value comes from function arguments directly
unsigned debug;

// Handler, checks whether gLabel implies one of the varset expressions, returns in gImplies
void allSatImpliesHandler(char* varset, int size) {
    if (!gImplies) {
        bdd thisbdd = bdd_true();
        for (int v = 0; v < size; ++v) {
            if (varset[v] == 1) {
                thisbdd = bdd_and(thisbdd, bdd_ithvar(v));
            }
            if (varset[v] == 0){
                thisbdd = bdd_and(thisbdd, bdd_nithvar(v));
            }
        }
        if (bdd_implies(thisbdd, bdd_ithvar(gLabel))){
            gImplies = true;
        }
    }
}

// Converts a given VWAA to SDBA, the main function of this class
spot::twa_graph_ptr make_semideterministic(VWAA *vwaa, unsigned debuginput) {
    
    debug = debuginput;

    // We first transform the VWAA into spot format

    // Creating helper files and saving current stream buffer
    std::ofstream outs;
    std::streambuf *coutbuf = std::cout.rdbuf();

    // Redirecting output into helper file and printing vwaa in hoa
    outs.open ("helper.hoa", std::ofstream::trunc);
    std::cout.rdbuf(outs.rdbuf());
    vwaa->print_hoaf();
    std::cout.rdbuf(coutbuf);
    outs.close();

    // Parsing the helper, acquiring spot format
    spot::parsed_aut_ptr pvwaaptr = parse_aut("helper.hoa", spot::make_bdd_dict());
    if (pvwaaptr->format_errors(std::cerr))
        return vwaa->spot_aut;  // todo Better error message
    if (pvwaaptr->aborted)
    {
        std::cerr << "--ABORT-- read\n";
        return vwaa->spot_aut;  // todo Better error message
    }
    auto pvwaa = pvwaaptr->aut;

    // We have VWAA parsed. Now, we assign Qmays and Qmusts and remove acceptance marks

    gnvwaa = pvwaa->num_states();

    const spot::bdd_dict_ptr& dict = pvwaa->get_dict();

    bool isqmay[gnvwaa];
    bool isqmust[gnvwaa];

    auto snvwaa = pvwaa->get_named_prop<std::vector<std::string>>("state-names");

    // We iterate over all states of the VWAA
    for (unsigned q = 0; q < gnvwaa; ++q)
    {
        if (debug == 1){std::cout << "State: " << (*snvwaa)[q] << " (" << q << ").\n";}
        if ((*snvwaa)[q].compare("t") == 0){
            gtnum = q;
            if (debug == 1){std::cout << "This is the {} state.\n";}
        }
        // Renaming state to its number instead of the LTL formula for later use
        (*snvwaa)[q] = std::to_string(q);


        isqmay[q] = false;
        bool thereIsALoop = false;
        // If there exists a looping, but not accepting outgoing edge, we set this state as Qmay
        for (auto& t: pvwaa->out(q))
        {
            for (unsigned d: pvwaa->univ_dests(t.dst))
            {
                if (t.src == d && t.acc.id == 0) {
                    isqmay[q] = true;
                    if (debug == 1){std::cout << "Qmay. ";} // It also may be Qmust
                    thereIsALoop = true;
                    break;
                }
            }
            if (thereIsALoop){ break; }
        }
        if (!isqmay[q]){
            if (debug == 1){std::cout << "Not Qmay. ";}
        }

        isqmust[q] = true;
        // If we find an outgoing edge, where there is no loop, we set this state as not Qmust and break the loop
        for (auto& t: pvwaa->out(q))
        {
            thereIsALoop = false;
            for (unsigned d: pvwaa->univ_dests(t.dst))
            {
                if (t.src == d){
                    thereIsALoop = true;
                }
            }
            if (!thereIsALoop){
                isqmust[q] = false;
                if (debug == 1){std::cout << "Not Qmust. ";}
                break;
            }
        }
        if (isqmust[q]) {
            if (debug == 1){std::cout << "Qmust. ";}
        }
        if (debug == 1){std::cout << "\n\n";}
    }

    // In gAlphabet variable, we store the set of all edge labels
    // (not only "a", "b", but also "and"-formulae: "a&b". not "a|b".)
    // Here, we create the alphabet by adding all possible labels using power-set construction
    if (debug == 1){ std::cout << "Setting the alphabet. "; }

    // pow(2, pvwaa->ap().size()) is the amount of all combinations of labels = num of letters in the final alphabet
    for (int i = 0; i < pow(2, pvwaa->ap().size()); i++){
        bdd thisbdd = bdd_true();
        // for all digits in the binary form of i
        for (int digit = 0; digit < pvwaa->ap().size(); digit++){
            if ((i & (int)pow(2, digit)) != 0){
                // add atomic proposition number digit
                thisbdd = bdd_and(thisbdd, bdd_ithvar(digit));
            } else {
                thisbdd = bdd_and(thisbdd, bdd_not(bdd_ithvar(digit)));
            }
        }
        gAlphabet.push_back(thisbdd);
    }

    if (debug == 1){
        std::cout << "It is: ";
        for (auto letter : gAlphabet){
            std::cout << letter;
        }
        std::cout << "\n";
    }

    // We now start building the SDBA by removing alternation, which gives us the final nondeterministic part
    spot::twa_graph_ptr sdba = spot::remove_alternation(pvwaa, true);
    //spot::twa_graph_ptr sdba = spot::remove_alternation(spot::make_twa_graph(pvwaa, {false, false, false, false, false, false}));
    bdd_extvarnum(gnvwaa);

    sdba->set_buchi();
    sdba->prop_state_acc(spot::trival(false));

    // Number of configurations C (states in the nondeterministic part)
    gnc = sdba->num_states();

    // Definition of the phis and Rs assigned to the states in the deterministic part, for future
    std::map<unsigned, std::set<std::string>> Rname;
    std::map<unsigned, bdd> phi1;
    std::map<unsigned, bdd> phi2;
    // State-names C are in style of "1,2,3", these represent states Q of the former VWAA configuration
    auto sn = sdba->get_named_prop<std::vector<std::string>>("state-names");
    std::set<std::string> C[gnc];

    // We mark the Rs of the states of ND part so we differ them from D part states with empty R, phi1 and phi2 later on
    // We also set all the edges in ND part of SDBA as not-accepting (also to fix odd behavior of remove_alternation)
    if (debug == 1) { std::cout << "\nRemoving acceptation from all edges in ND part"; }

    for (unsigned ci = 0; ci < gnc; ++ci) {
        Rname[ci] = {"ND-part state"};

        for (auto &t: sdba->out(ci)) {
            for (unsigned d: pvwaa->univ_dests(t.dst)) {
                if (debug == 1) {std::cout << "\nEdge of sdba: " << t.src << "-" << d << " acceptation: " << t.acc << ". "; }
                t.acc = 0;
                if (debug == 1) { std::cout << "We set acc to " << t.acc << ". "; }
            }
        }
    }
    if (debug == 1) { std::cout << "\n"; }

    // Choosing the R

    // We go through all the states in C
    // In each one, we go through all its Q-s and build all possible R-s based on what types of states Q-s are
    // For each R - if it is a new R, we build an R-component
    for (unsigned ci = 0; ci < gnc; ++ci) {

        // We parse the statename ((*sn)[ci]) to create a set of states
        if (sn && ci < sn->size() && !(*sn)[ci].empty()) {
            std::string s = ((*sn)[ci]) + ",";
            std::string delimiter = ",";
            size_t pos = 0;
            std::string token;
            while ((pos = s.find(delimiter)) != std::string::npos) {
                token = s.substr(0, pos);
                C[ci].insert(token);
                s.erase(0, pos + delimiter.length());
            }
        } else {
            std::cout << "Wrong C state name."; // todo better error message
        }
        if (((*sn)[ci]).compare("{}") == 0){
            if (debug == 1) { std::cout << "\nStarting check of configuration of state {}, renaming state to: " << std::to_string(gtnum); }
            ((*sn)[ci]) = std::to_string(gtnum);
            C[ci].clear();
            C[ci].insert(std::to_string(gtnum));
        }

        std::set<std::string> R;

        if (debug == 1){
            std::cout << "\nChecking if configuration " << ci << " = {";
            for (auto x : C[ci]){
                std::cout << " " << x;
            }
            std::cout << " } contains only valid states.\n";
        }
        // Check if only states reachable from Qmays are in C. If not, this configuration can not contain an R.
        if (checkMayReachableStates(pvwaa, C[ci], R, isqmay)){  // We are using R just as a placeholder empty set here
            R.clear();
            if (debug == 1){std::cout << "Yes! \n";}
            // We call this function to judge Q-s of this C and create R-s and R-components based on them
            createDetPart(pvwaa, ci, C[ci], C[ci], R, isqmay, isqmust, sdba, Rname, phi1, phi2);
        }
    }


    if (debug == 1) {
        std::cout << "\nRECAPITULATION of states and phis";
        for (unsigned c = 0; c < sdba->num_states(); ++c) {
            std::cout << "\nC: " << c;
            if (c < gnc){
                std::cout << " = {";
                for (auto x : C[c]) {
                    std::cout << " " << x;
                }
                std::cout << " }";
            } else {
                std::cout << " Rname: ";
                for (auto x : Rname[c]) {
                    std::cout << x << ", ";
                }
                // xz maybe this caused errors?
                std::cout << "phi1: " << (bdd) phi1[c] << ", phi2: " << (bdd) phi2[c];

            }
        }
        std::cout << "\n\n";
    }


    // Call spot's merge edges function
    sdba->merge_edges();

    sdba->set_buchi();
    sdba->prop_state_acc(spot::trival(false));

    // Automaton is universal if the conjunction between the labels of two transitions leaving a state is
    // always false.
    sdba->prop_universal(spot::trival());
    // automaton is complete if for each state the union of the labels of its outgoing transitions
    // is always true.
    sdba->prop_complete(spot::trival());

    return sdba;
}

bool checkMayReachableStates(std::shared_ptr<spot::twa_graph> vwaa, std::set<std::string> Conf,
                             std::set<std::string> Valid, bool isqmay[]){

    // We check each state whether it is Qmay. If it is, we add it to Valid with all successors
    for (auto q : Conf)
    {
        if (q.empty() || !isdigit(q.at(0))){
            std::cout << "We are in BADSTATE: " << q << ". "; // todo Better error message
        } else {
            if (isqmay[std::stoi(q)]) {
                addToValid(vwaa, q, Valid);
            }
        }
    }

    // We check and return whether all states in Conf are valid (QMays and their successors)
    for (auto q : Conf)
    {
        if (!(Valid.find(q) != Valid.end())){
            return false;
        }
    }
    return true;
}

void addToValid(std::shared_ptr<spot::twa_graph> vwaa, std::string q, std::set<std::string> &Valid){
    Valid.insert(q);
    // We add into Valid all states reachable from q too
    for (auto &t: vwaa->out((unsigned int)std::stoi(q))) {
        for (unsigned d: vwaa->univ_dests(t.dst)) {
            // We exclude loops for effectivity, as they never need to be checked to be added again
            if (std::to_string(d) != q) {
                addToValid(vwaa, std::to_string(d), Valid);
            }
        }
    }
}

void createDetPart(std::shared_ptr<spot::twa_graph> vwaa, unsigned ci, std::set<std::string> Conf,
                   std::set<std::string> remaining, std::set<std::string> R, bool isqmay[], bool isqmust[],
                   spot::twa_graph_ptr &sdba, std::map<unsigned, std::set<std::string>> &Rname,
                   std::map<unsigned, bdd> &phi1, std::map<unsigned, bdd> &phi2){

    // We choose first q that comes into way
    auto it = remaining.begin();
    std::string q;
    if (it != remaining.end()) q = *it;

    if (debug == 1){std::cout << "\nFunction createDetPart.\nWe chose q: " << q << ". ";}
    // Erase it from remaining as we are checking it now
    remaining.erase(q);

    // Checking state correctness
    if (q.empty() || !isdigit(q.at(0))){
        std::cout << "We are in BADSTATE: " << q << ". "; // todo Better error message
    } else {
        // If this state is Qmust, we add it (and don't have to check Qmay)
        if (isqmust[std::stoi(q)]){
            if (debug == 1){std::cout << "It is Qmust, adding to R. ";}
            if (R.count(q) == 0) {
                R.insert(q);
            }
        } else {
            // If it is Qmay, we recursively call the function and try both adding it and not
            if (isqmay[std::stoi(q)]){
                if (debug == 1){std::cout << "It is Qmay (and not Qmust!), adding to R";}

                // We create a new branch with new R and add the state q to this R
                std::set<std::string> Rx = R;
                if (Rx.count(q) == 0) {
                    Rx.insert(q);
                }

                if (!remaining.empty()){
                    // We run the branch that builds the R where this state is added
                    if (debug == 1){std::cout << " and creating branch including: " << q << ".\n";}
                    createDetPart(vwaa, ci, Conf, remaining, Rx, isqmay, isqmust, sdba, Rname, phi1, phi2);
                } else{
                    // If this was the last state, we have one R complete. Let's build an R-component from it.
                    if (debug == 1){std::cout << " and this was lastx state!\n----------> \nCreate Rx comp: \n";}
                    createRComp(vwaa, ci, Conf, Rx, sdba, Rname, phi1, phi2);
                }
                // We also continue this run without adding this state to R - representing the second branch
                if (debug == 1){std::cout<< "Also continuing for not adding q to R - ";}
            }
        }
        if (debug == 1){std::cout << "Done checking for q: " << q;}

    }
    if (debug == 1){std::cout << "\n Is this last state? ";}
    // If this was the last state, we have this R complete. Let's build an R-component from it.
    if (remaining.empty()){
        if (debug == 1){std::cout << " YES!  \n----------> \nCreate R comp: \n";}
        createRComp(vwaa, ci, Conf, R, sdba, Rname, phi1, phi2);
    } else{
        if (debug == 1){std::cout << " NO! Check another: \n";}
        createDetPart(vwaa, ci, Conf, remaining, R, isqmay, isqmust, sdba, Rname, phi1, phi2);
    }
}

void createRComp(std::shared_ptr<spot::twa_graph> vwaa, unsigned ci, std::set<std::string> Conf,
                 std::set<std::string> R, spot::twa_graph_ptr &sdba, std::map<unsigned, std::set<std::string>> &Rname,
                 std::map<unsigned, bdd> &phi1, std::map<unsigned, bdd> &phi2){
    if (debug == 1){ std::cout << "\n~~~~~~Beginning of function createRComp:"; }

    // The phis of this state
    bdd p1;
    bdd p2;

    // To distinguish between an empty bdd and a bdd containing "false", we create these bools
    bool p1empty;
    bool p2empty;

    // First we construct the edges from C into the R component by getting the correct phi1 and phi2

    // For each edge label ("a,b,c", "a,b,!c", "a,!b,c"...) of the alphabet
    for (auto label : gAlphabet){

        if (debug == 1) {
            std::cout << "\n\n---For Conf: ";
            for (auto x : Conf){
                std::cout << x << ",";
            }
            std::cout << " R: ";
            for (auto y : R){
                std::cout << y << ",";
            }
            std::cout << " starting createRcomp loop under label: " << label << "\n";
        }

        p1 = bdd_false();
        p2 = bdd_false();

        // We mark both phis as empty
        p1empty = true;
        p2empty = true;

        for (unsigned q = 0; q < gnvwaa; ++q) {

            if (debug == 1) { std::cout << "\nChecking q: " << q << " (for label: " << label << ") to add to phis: "; }

            // We check all states of Conf
            if (Conf.find(std::to_string(q)) != Conf.end()){

                // For each such state, we add its successors through m.t. to phi1 using and
                if (debug == 1) { std::cout << "\n  It is in conf. Adding its m.t.-successors under this label to phi1."; }

                if (p1 == bdd_false()) {
                    // If the bdd is false, we only add if it's empty
                    if (p1empty){
                        if (debug == 1) { std::cout << "\n  P1 is empty. Adding succ of this q to p1 even though it is false currently."; }
                        p1empty = false;
                        p1 = getqSuccs(vwaa, Conf, R, q, label);
                    }
                } else {
                    p1 = bdd_and(p1, getqSuccs(vwaa, Conf, R, q, label));
                }
                if (debug == 1) { std::cout << "\n  Added all m.t.-successors under this label to phi1. Got: " << p1; }
            }

            // We add all q-s of R to phi2
            if (R.find(std::to_string(q)) != R.end()) {
                if (debug == 1) { std::cout << "\n  q is in R, adding q to phi2."; }
                if (p2 == bdd_false()) {
                    // If the bdd is false, we only add if it's empty
                    if (p2empty){
                        if (debug == 1) { std::cout << "\n  P2 is empty. Adding q to p2 even though it is false currently."; }
                        p2empty = false;
                        p2 = bdd_ithvar(q);
                    }
                } else {
                    p2 = bdd_and(p2, bdd_ithvar(q));
                }
            }
            if (debug == 1) { std::cout << "\n"; }
        }

        if (debug == 1) {
            std::cout << "\nTo be sure, states of R: ";
            for (auto y : R) {
                std::cout << y << ", ";
            }
        }

        // We now substitute all states succp1 of R with true
        if (debug == 1) {  std::cout << "Replacing all states of phi1 (" << p1 << ") in R with true.\n"; }
        p1 = subStatesOfRWithTrue(p1, R);
        if (debug == 1) {
            std::cout << "\nThe phis we just made: phi1: " << p1 << ", phi2: " << p2 << " (for R: ";
            for (auto x : R){
                std::cout << x << ", ";
            }
            std::cout << ")\n";
        }


        // We need to check if this R-component state exists already
        // addedStateNum is the number of the state if it exists, else value remains as a "new state" number:
        unsigned addedStateNum = sdba->num_states();
        if (debug == 1) { std::cout << "Checking if the R-comp with same R, phi1 and phi2 exists. ";}

        for (unsigned c = 0; c < sdba->num_states(); ++c) {
            if (Rname[c] == R && phi1[c] == p1 && phi2[c] == p2){
                addedStateNum = c;
                if (debug == 1) { std::cout << " It exists!"; }
                break;
            }
        }

        if (debug == 1) { std::cout << "\nThe statenum is: " << addedStateNum << "\n";}

        // If phi1 is false, all the followers will be false too and no state will be accepting, so we don't need to try.
        if (p1 != bdd_false()) {
            // If the state doesn't exist yet, we create it with "sdba->num_states()-1" becoming its new number.
            if (addedStateNum == sdba->num_states()) {
                if (debug == 1) {
                    std::cout << "\nThis state is new, creating it, with edge from C" << ci << " to C"
                              << addedStateNum << " labeled " << label;
                }
                sdba->new_state(); // addedStateNum is now equal to sdba->num_states()-1 todo vwaa also adds a state for some reason
                Rname[sdba->num_states() - 1] = R;
                phi1[sdba->num_states() - 1] = p1;
                phi2[sdba->num_states() - 1] = p2;
                //(*(sdba->get_named_prop(<std::vector<std::string>>("state-names")))[sdba->num_states()-1] = "New"; //todo name states?
                sdba->new_edge(ci, addedStateNum, label, {});
                //bdd_extvarnum(1);

            } else {
                bool connected = false;
                // If the state already exists, we check if there is an edge leading there from the current state
                for (auto &t: sdba->out(ci)) {
                    // If there is such an edge, we add this label via "OR" to the bdd
                    if (t.dst == addedStateNum) {
                        if (debug == 1) {
                            std::cout << "Adding new label to the edge under OR: " << t.src << "-" << t.dst
                                      << " bdd:" << t.cond << " label: " << label << ". \n";
                        }
                        connected = true;
                        t.cond = bdd_or(t.cond, label);
                    }
                }
                // If there isn't such an edge, we create a new one
                if (!connected) {
                    // We connect the state to this configuration under the currently checked label
                    if (debug == 1) {
                        std::cout << "New edge from C" << ci << " to C" << addedStateNum << " labeled "
                                  << label;
                    }
                    sdba->new_edge(ci, addedStateNum, label, {});
                }
            }

            // If the state is new, add all successors of this state to the SDBA and connect them
            if (addedStateNum == sdba->num_states() - 1) {
                if (debug == 1) { std::cout << "\nAs the state is new, adding all succs"; }
                addRCompStateSuccs(vwaa, sdba, addedStateNum, Conf, Rname, phi1, phi2);
            }

        } else {
            if (debug == 1) { std::cout << "\nPhi1 is false, so we are not adding this state.\n";}
        }
    }
}


// Adds successors of state statenum (and their successors, recursively)
void addRCompStateSuccs(std::shared_ptr<spot::twa_graph> vwaa, spot::twa_graph_ptr &sdba, unsigned statenum,
                        std::set<std::string> Conf, std::map<unsigned, std::set<std::string>> &Rname,
                        std::map<unsigned, bdd> &phi1, std::map<unsigned, bdd> &phi2){

    if (debug == 1){
        std::cout << "\n\n__Beginning addRCompStateSuccs for Conf: ";
        for (auto x : Conf){
            std::cout << x << ", ";
        }
        std::cout << ". Checking succs of " << statenum << " - R: ";
        for (auto x : Rname[statenum]){
            std::cout << x << ", ";
        }
        std::cout << "phi1: " << phi1[statenum] << ", phi2: " << phi2[statenum] << ")\n";
    }

    // The R and phis of the state we are adding successors of
    std::set<std::string> R = Rname[statenum];
    bdd p1 = phi1[statenum];
    bdd p2 = phi2[statenum];

    // The phis for the successor state (will reset for each added state)
    bdd succp1;
    bdd succp2;


    // For each edge label of the alphabet we compute phis of the reached state (succp1 and succp2)
    for (auto label : gAlphabet) {

        if (debug == 1) { std::cout << "\n\n   In addRCompStateSuccs loop for state " << statenum << ", checking label: " << label << "\n"; }
        succp1 = p1;
        succp2 = p2;

        if (debug == 1) { std::cout << ">Replacing all states of succphi1 (" << succp1 << ") with their successors:\n"; }
        s_bddPair* pair = bdd_newpair();
        for (unsigned q = 0; q < gnvwaa; q++){
            // For each state q in succphi1
            if (debug == 1) { std::cout << "\nchecking if succp1" << succp1 << " implies q " << q << " (" << bdd_ithvar(q) << ")."; }

            // "if (bdd_implies(succp1, bdd_ithvar(q)))" is not enough if succp1 contains disjunctions, so we use handlers
            gImplies = false;
            gLabel = q;
            bdd_allsat(succp1, allSatImpliesHandler);
            if (gImplies){
                if (debug == 1) { std::cout << " yes"; }
                s_bddPair* newPair = bdd_newpair();
                bdd_setbddpair(newPair, q, getqSuccs(vwaa, Conf, R, q, label));
                pair = bdd_mergepairs(pair, newPair);
            }
        }
        // Replace all first parts of pairs with the second (replacing all q-s with their successors)
        succp1 = bdd_veccompose(succp1, pair);
        if (debug == 1) { std::cout << ">New succphi1:" << succp1 << "\n"; }

        // Substitute states succp1 of R with true
        succp1 = subStatesOfRWithTrue(succp1, R);

        if (debug == 1) { std::cout << ">Edited succphi1:" << succp1 << "\n"; }

        // The same for succphi2 (except substituting states of R with true)
        if (debug == 1) { std::cout << "Replacing all states of succphi2 (" << succp2 << ") with their successors:\n"; }
        pair = bdd_newpair();
        for (unsigned q = 0; q < gnvwaa; q++){

            gImplies = false;
            gLabel = q;
            bdd_allsat(succp2, allSatImpliesHandler);
            if (gImplies){
                s_bddPair* newPair = bdd_newpair();
                bdd_setbddpair(newPair, q, getqSuccs(vwaa, Conf, R, q, label));
                pair = bdd_mergepairs(pair, newPair);
            }
        }
        succp2 = bdd_veccompose(succp2, pair);

        // xz maybe this caused errors?
        if (debug == 1) { std::cout << "\nDone creating succphis for state " << statenum << " under label " << label
                                      << ". Succphi1: " << succp1 << ", succphi2 : " << succp2 << "\n"; }



        bool accepting = false;

        if (succp1 == bdd_true()) {
            // We make this the breakpoint and change succp1 and succp2 completely
            if (debug == 1) { std::cout << "Succphi1 is true, making a breakpoint, setting Succphi1 to Succphi2.\n"; }

            succp1 = succp2;
            succp1 = subStatesOfRWithTrue(succp1, R);

            if (debug == 1) { std::cout << "Also changing succphi2 to all states of R.\n"; }
            succp2 = bdd_false();
            for (auto qs : R) {
                if (succp2 == bdd_false()){
                    succp2 = bdd_ithvar(stoi(qs));
                } else {
                    succp2 = bdd_and(succp2, bdd_ithvar(stoi(qs)));
                }
            }
            accepting = true;
        }

        // xz maybe this caused errors?
        // We finished constructing succphi1 and succphi2, we can start creating the R-component based on them
        if (debug == 1) {
            std::cout << "We constructed succphi1: " << succp1 << ", succphi2: " << succp2 << " (under R: ";
            for (auto x : R) {
                std::cout << x << ", ";
            }
            std::cout << ")\n";
        }

        // We need to check if this R-component state exists already
        // succStateNum is the number of the state if it exists, else value remains as a "new state" number:
        unsigned succStateNum = sdba->num_states();

        bool existsAlready = false;

        // If succp1 is false, we do not add the state/edge, as this branch would never accept anyway
        if (succp1 != bdd_false()) {

            if (debug == 1) { std::cout << "\nChecking configurations to find one with same Rname, phi1 and phi2."; }
            for (unsigned c = 0; c < sdba->num_states(); ++c) {
                if (Rname[c] == R && phi1[c] == succp1 && phi2[c] == succp2) {
                    succStateNum = c;
                    existsAlready = true;
                    if (debug == 1) { std::cout << " It exists!"; }
                    break;
                }
            }
            if (debug == 1) { std::cout << "\nOur fitting successor state is state: " << succStateNum << "\n"; }

            // If the state doesn't exist yet, we create it with "sdba->num_states()-1" becoming its new number
            if (succStateNum == sdba->num_states()) {   // the same as "if !existsAlready"
                sdba->new_state();         // succStateNum is now equal to sdba->num_states()-1
                Rname[succStateNum] = R;
                phi1[succStateNum] = succp1;
                phi2[succStateNum] = succp2;
                //bdd_extvarnum(1);

                // xz maybe this caused errors?
                if (debug == 1) {
                    std::cout << "This state is new. State num: " << succStateNum << ", R: ";
                    for (auto x : R) {
                        std::cout << x << ", ";
                    }
                    std::cout << "succp1: " << succp1 << ", succp2: " << succp2 << ", SDBA num states: "
                              << sdba->num_states() << "\n";
                    std::cout << "Also creating edge from C" << statenum << " to C"
                              << succStateNum << " labeled " << label;
                }
                // (*(sdba->get_named_prop<std::vector<std::string>>("state-names")))[sdba->num_states()-1] = "New"; todo name states?
                if (accepting) {
                    sdba->new_edge(statenum, succStateNum, label, {0});
                    if (debug == 1) { std::cout << ", acc {0}. "; }
                } else {
                    sdba->new_edge(statenum, succStateNum, label, {});
                    if (debug == 1) { std::cout << ", acc {}. "; }
                }
                if (debug == 1) { std::cout << "\n"; }
            } else {
                bool connected = false;
                if (debug == 1) { std::cout << "This state exists, checking if this edge is new\n"; }
                // If the state already exists, we check if there is a same-acc edge leading there from the current state
                for (auto &t: sdba->out(statenum)) {
                    // If there is such an edge, we add it as OR to the existing edge instead of creating a new edge
                    if (t.dst == succStateNum && (((t.acc != 0 && accepting) || (t.acc == 0 && !accepting)))) {
                        if (debug == 1) {
                            std::cout << "Adding new label to the edge " << t.src << "-" << t.dst
                                      << " under OR. Adding " << label << " to " << t.cond << ", acc " << t.acc << "\n";
                        }
                        connected = true;
                        t.cond = bdd_or(t.cond, label);
                    }
                }
                // If there isn't such an edge, we create a new one
                if (!connected) {
                    if (accepting) {
                        if (debug == 1) {
                            std::cout << "There is not an edge " << statenum << "-" << succStateNum
                                      << " under label " << label << ", acc {0}. Creating it.\n";
                        }
                        sdba->new_edge(statenum, succStateNum, label, {0});
                    } else {
                        if (debug == 1) {
                            std::cout << "There is not an edge " << statenum << "-" << succStateNum
                                      << " under label " << label << ", acc {}. Creating it.\n";
                        }
                        sdba->new_edge(statenum, succStateNum, label, {});
                    }
                }
            }

            // If the state is new and phi1 is not false, add all further successors of this state to SDBA and connect them
            if (!existsAlready) {
                if (succp1 != bdd_false()) {
                    if (debug == 1) { std::cout << "This state is new and its Phi1 != false, we are adding its succs.\n"; }
                    addRCompStateSuccs(vwaa, sdba, succStateNum, Conf, Rname, phi1, phi2);
                } else {
                    // xz maybe this caused errors?
                    if (debug == 1) { std::cout << "Phi1 (" << succp1 << ") of this state is false, so we do not add succs. \n"; }
                }
            } else {
                if (debug == 1) { std::cout << "This state already exists, not adding its succs. \n"; }
            }
        } else {
            if (debug == 1) { std::cout << "\nPhi1 is false, not adding this succstate.\n"; }
        }

    }
    if (debug == 1) { std::cout << "\n<<<<<<   End of function addRCompStateSuccs of state " << statenum << "\n"; }
}


// Gets the bdd of successors of q under label belonging to m.t. relation
bdd getqSuccs(std::shared_ptr<spot::twa_graph> vwaa, std::set<std::string> Conf, std::set<std::string> R, unsigned q,
              bdd label){

    if (debug == 1) { std::cout << "\nGetting succs of state " << q << " under label " << label << "\n"; }

    bdd succbdd = bdd_false();
    bdd edgebdd = bdd_false();

    bool edgeEmpty;

    // If edge under label is a correct m.t., add its follower to succbdd

    // For the transition to be a correct m.t., q either needs to not be in R, or see below *
    if ((R.find(std::to_string(q)) == R.end())) {
        if (debug == 1) { std::cout << "Q is not in R."; }
        // Find the edge under "label"
        for (auto &t: vwaa->out(q)) {
            if (debug == 1) { std::cout << "\nEdge from " << t.src; }
            edgebdd = bdd_false();
            bool edgeEmpty = true;
            // For each destination of an alternating edge, we connect the correct destinations under AND
            for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                if (debug == 1) {
                    std::cout << "\nEdge " << t.src << "-" << tdst << " t.cond: " << t.cond << ", label: " << label << ". \n";
                }
                // If t.cond contains this label as one of the conjunctions and tdst is still a vwaa state ( todo this is not needed if vwaa getting more states gets fixed)
                if (bdd_implies(label, t.cond) && (tdst < gnvwaa)) {
                    if (debug == 1) { std::cout << "<- the label is right. "; }

                    // Add this successor of q
                    // If this state is {}, add bdd_true instead

                    if (edgebdd == bdd_false()){
                        // If the bdd is false, we only add if it's empty
                        if (edgeEmpty){
                            edgeEmpty = false;
                            if (tdst == gtnum){
                                if (debug == 1) { std::cout << "This is the {} state, creating edgebdd as true"; }
                                edgebdd = bdd_true();
                            } else {
                                if (debug == 1) { std::cout << "Creating edgebdd as tdst (" << tdst << ")"; }
                                edgebdd = bdd_ithvar(tdst);
                            }
                        }
                    } else {
                        if (tdst == gtnum){
                            if (debug == 1) { std::cout << "This is the {} state, adding true to edgebdd"; }
                            edgebdd = bdd_true();
                        } else {
                            if (debug == 1) { std::cout << "Adding tdst (" << tdst << ") to edgebdd"; }
                            edgebdd = bdd_and(edgebdd, bdd_ithvar(tdst));
                        }
                    }
                }
            }

            if (debug == 1) { std::cout << "\nAdding edgebdd " << edgebdd << " to succbdd " << succbdd << " under OR"; }
            // We connect the destinations of this edge to the bdd under OR
            succbdd = bdd_or(succbdd, edgebdd);
            if (debug == 1) { std::cout << "\nGetting succbdd " << succbdd << "\n"; }
        }
    } else { // * or q must be in Conf && edge must not be accepting
        if (debug == 1) { std::cout << "Q is in R."; }
        if (Conf.find(std::to_string(q)) != Conf.end()) {
            if (debug == 1) { std::cout << "\nQ is in Conf."; }
            // Find the edge under "label"
            for (auto &t: vwaa->out(q)) {
                if (debug == 1) {
                    std::cout << "\nEdge from " << t.src;
                }
                edgebdd = bdd_false();
                edgeEmpty = true;
                for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                    if (debug == 1) {
                        std::cout << "\n Edge " << t.src << "-" << tdst << " t.cond: " << t.cond << ", label: " << label << ".";
                    }
                    // If t.cond contains this label as one of the conjunctions and tdst is still a vwaa state ( todo this is not needed if vwaa getting more states gets fixed)
                    if (bdd_implies(label, t.cond) && (tdst < gnvwaa)) {
                        if (debug == 1) { std::cout << "\n  <- the label is right "; }

                        if (t.acc == 0) {
                            if (debug == 1) { std::cout << "and it is not accepting. "; }

                            if (edgebdd == bdd_false()){
                                // If the bdd is false, we only add if it's empty
                                if (edgeEmpty) {
                                    edgeEmpty = false;
                                    if (tdst == gtnum) {
                                        if (debug == 1) {
                                            std::cout << "This is the {} state, creating edgebdd as true";
                                        }
                                        edgebdd = bdd_true();
                                    } else {
                                        if (debug == 1) { std::cout << "Creating edgebdd as tdst (" << tdst << ")"; }
                                        edgebdd = bdd_ithvar(tdst);
                                    }
                                }
                            } else {
                                if (tdst == gtnum){
                                    if (debug == 1) { std::cout << "This is the {} state, adding true to edgebdd"; }
                                    edgebdd = bdd_true();
                                } else {
                                    if (debug == 1) { std::cout << "Adding tdst (" << tdst << ") to edgebdd"; }
                                    edgebdd = bdd_and(edgebdd, bdd_ithvar(tdst));
                                }
                            }
                        }
                    }
                }

                // We connect the destinations of this edge to the bdd under OR
                if (debug == 1) { std::cout << "\nAdding edgebdd " << edgebdd << " to succbdd " << succbdd << " under OR"; }
                succbdd = bdd_or(succbdd, edgebdd);
                if (debug == 1) { std::cout << "\nGetting succbdd " << succbdd << "\n"; }
            }
        }
    }
    if (debug == 1) { std::cout << "\nAdded all succs of " << q << " under " << label << ", got: " << succbdd << "\n"; }

    return succbdd;
}

bdd subStatesOfRWithTrue(bdd phi, std::set<std::string> R){

    if (debug == 1) { std::cout << "\nReplacing all states of R with true in " << phi; }

    // If this phi is false, we return false or we'd get weird results (as implication from false is true)
    if (phi != bdd_false()) {
        // For all states of Q, find those that are in Phi
        if (debug == 1) { std::cout << "\nChecking q-s"; }
        for (unsigned q = 0; q < gnvwaa; q++) {
            if (debug == 1) { std::cout << ". " << q; }

            if (bdd_implies(phi, bdd_ithvar(q))) {
                // xz maybe this caused errors?
                if (debug == 1) { std::cout << " - it's in " << phi; }

                if ((R.find(std::to_string(q)) != R.end())) {
                    if (debug == 1) { std::cout << ".\n It's in R. Recomposing it as true"; }
                    // Replace q with true
                    phi = bdd_compose(phi, bdd_true(), q);
                }
            }
        }
    }
    if (debug == 1) { std::cout << "\n"; }
    return phi;
}