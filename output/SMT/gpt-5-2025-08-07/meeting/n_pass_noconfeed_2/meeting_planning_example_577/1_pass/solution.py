import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def min_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    HA = "Haight-Ashbury"
    RH = "Russian Hill"
    FW = "Fisherman's Wharf"
    NH = "Nob Hill"
    GGP = "Golden Gate Park"
    AS = "Alamo Square"
    PH = "Pacific Heights"

    # People: id -> (name, location, (avail_start, avail_end), min_duration)
    people = {
        1: ("Stephanie", RH, (minutes(20,0), minutes(20,45)), 15),
        2: ("Kevin", FW, (minutes(19,15), minutes(21,45)), 75),
        3: ("Robert", NH, (minutes(7,45), minutes(10,30)), 90),
        4: ("Steven", GGP, (minutes(8,30), minutes(17,0)), 75),
        5: ("Anthony", AS, (minutes(7,45), minutes(19,45)), 15),
        6: ("Sandra", PH, (minutes(14,45), minutes(21,45)), 45),
    }

    # Travel times in minutes (asymmetric where given)
    travel = {
        (HA, RH): 17, (HA, FW): 23, (HA, NH): 15, (HA, GGP): 7, (HA, AS): 5, (HA, PH): 12,
        (RH, HA): 17, (RH, FW): 7, (RH, NH): 5, (RH, GGP): 21, (RH, AS): 15, (RH, PH): 7,
        (FW, HA): 22, (FW, RH): 7, (FW, NH): 11, (FW, GGP): 25, (FW, AS): 20, (FW, PH): 12,
        (NH, HA): 13, (NH, RH): 5, (NH, FW): 11, (NH, GGP): 17, (NH, AS): 11, (NH, PH): 8,
        (GGP, HA): 7, (GGP, RH): 19, (GGP, FW): 24, (GGP, NH): 20, (GGP, AS): 10, (GGP, PH): 16,
        (AS, HA): 5, (AS, RH): 13, (AS, FW): 19, (AS, NH): 11, (AS, GGP): 9, (AS, PH): 10,
        (PH, HA): 11, (PH, RH): 7, (PH, FW): 13, (PH, NH): 8, (PH, GGP): 15, (PH, AS): 10,
    }

    def ttime(loc_a, loc_b):
        return travel[(loc_a, loc_b)]

    start_time_at_HA = minutes(9, 0)
    start_location = HA

    n_people = len(people)
    slots = n_people  # up to one slot per person

    # Z3 variables
    opt = Optimize()

    slot_person = [Int(f"slot_person_{i}") for i in range(slots)]
    start = [Int(f"start_{i}") for i in range(slots)]
    end = [Int(f"end_{i}") for i in range(slots)]
    selected = {p: Bool(f"selected_{p}") for p in people.keys()}

    # Domains
    for i in range(slots):
        opt.add(And(slot_person[i] >= 0, slot_person[i] <= n_people))
        opt.add(And(start[i] >= 0, start[i] <= 24*60))
        opt.add(And(end[i] >= 0, end[i] <= 24*60))
        opt.add(end[i] >= start[i])

    # Once a zero slot appears, all subsequent must be zero (pack meetings at the front)
    for i in range(slots-1):
        opt.add(Implies(slot_person[i] == 0, slot_person[i+1] == 0))

    # If a slot is unused, set times to end of day (no effect)
    for i in range(slots):
        opt.add(Implies(slot_person[i] == 0, And(start[i] == 24*60, end[i] == 24*60)))

    # Each person appears at most once; link to selected
    for p in people.keys():
        count_p = Sum([If(slot_person[i] == p, 1, 0) for i in range(slots)])
        opt.add(Or(selected[p] == True, selected[p] == False))
        opt.add(count_p == If(selected[p], 1, 0))

    # Meeting constraints per slot based on assigned person
    for i in range(slots):
        for p, pdata in people.items():
            name, loc, (avail_s, avail_e), min_dur = pdata
            opt.add(Implies(slot_person[i] == p, And(
                start[i] >= avail_s,
                end[i] <= avail_e,
                end[i] - start[i] >= min_dur
            )))

    # Travel constraints between consecutive used slots
    for i in range(1, slots):
        for p_prev, pdata_prev in people.items():
            loc_prev = pdata_prev[1]
            for p_curr, pdata_curr in people.items():
                loc_curr = pdata_curr[1]
                opt.add(Implies(And(slot_person[i-1] == p_prev, slot_person[i] == p_curr),
                                start[i] >= end[i-1] + ttime(loc_prev, loc_curr)))

    # Travel from start (HA at 9:00) to first used slot
    for p, pdata in people.items():
        loc = pdata[1]
        opt.add(Implies(slot_person[0] == p, start[0] >= start_time_at_HA + ttime(start_location, loc)))

    # Objective 1: maximize number of people met
    total_met = Sum([If(selected[p], 1, 0) for p in people.keys()])
    h1 = opt.maximize(total_met)

    # Objective 2: maximize total meeting time
    total_meeting_time = Sum([If(slot_person[i] == 0, 0, end[i] - start[i]) for i in range(slots)])
    h2 = opt.maximize(total_meeting_time)

    # Optional: minimize finish time of last meeting (encourage earlier end if equal)
    # last_end = the end time of the last non-zero slot; since zeros are packed at end with end=1440,
    # we can minimize the maximum end among used slots negatively to break ties
    # Here we just add a slight preference: minimize waiting by minimizing sum of gaps (not strictly necessary)
    # We'll minimize the sum of start times of used slots to push earlier starts (soft tie-break)
    sum_starts = Sum([If(slot_person[i] == 0, 0, start[i]) for i in range(slots)])
    h3 = opt.minimize(sum_starts)

    if opt.check() != sat:
        # In the unlikely event of unsat, output empty itinerary
        print(json.dumps({"itinerary": []}, indent=2))
        return

    model = opt.model()

    # Build itinerary
    itinerary = []
    for i in range(slots):
        pval = model[slot_person[i]].as_long()
        if pval == 0:
            break
        name, loc, _, _ = people[pval]
        s = model[start[i]].as_long()
        e = model[end[i]].as_long()
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": min_to_str(s),
            "end_time": min_to_str(e)
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()