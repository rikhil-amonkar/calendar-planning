import json
from z3 import *

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    locations = ["Nob Hill", "Presidio", "North Beach", "Fisherman's Wharf", "Pacific Heights"]

    # People and their constraints
    people = {
        1: {"name": "Jeffrey", "loc": "Presidio", "win_start": 8*60, "win_end": 10*60, "min": 105},
        2: {"name": "Steven", "loc": "North Beach", "win_start": 13*60 + 30, "win_end": 22*60, "min": 45},
        3: {"name": "Barbara", "loc": "Fisherman's Wharf", "win_start": 18*60, "win_end": 21*60 + 30, "min": 30},
        4: {"name": "John", "loc": "Pacific Heights", "win_start": 9*60, "win_end": 13*60 + 30, "min": 15},
    }

    # Travel times (in minutes), directional
    travel_times = {
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Pacific Heights"): 8,

        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Pacific Heights"): 11,

        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,

        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Pacific Heights"): 12,

        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
    }

    # Helper maps
    person_ids = list(people.keys())
    person_to_location = {pid: people[pid]["loc"] for pid in person_ids}

    # Start info
    start_location = "Nob Hill"
    start_time = 9 * 60  # 9:00

    # Travel time matrices for person indices
    travel_from_start = {pid: travel_times[(start_location, person_to_location[pid])] for pid in person_ids}

    travel_matrix = {}
    for p in person_ids:
        for q in person_ids:
            loc_p = person_to_location[p]
            loc_q = person_to_location[q]
            if loc_p == loc_q:
                t = 0  # no travel needed within same location
            else:
                t = travel_times.get((loc_p, loc_q))
                if t is None:
                    raise KeyError(f"Missing travel time from {loc_p} to {loc_q}")
            travel_matrix[(p, q)] = t

    # Z3 Optimize context
    opt = Optimize()

    num_slots = 4
    person = [Int(f"person_{i}") for i in range(num_slots)]
    start = [Int(f"start_{i}") for i in range(num_slots)]
    end = [Int(f"end_{i}") for i in range(num_slots)]

    # Variable domains
    for i in range(num_slots):
        opt.add(And(person[i] >= 0, person[i] <= 4))
        opt.add(And(start[i] >= 0, start[i] <= 24*60))
        opt.add(And(end[i] >= 0, end[i] <= 24*60))

    # If slot empty, times are zero
    for i in range(num_slots):
        opt.add(Implies(person[i] == 0, And(start[i] == 0, end[i] == 0)))

    # Meeting window and duration constraints per slot based on selected person
    for i in range(num_slots):
        implies_list = []
        for pid in person_ids:
            win_s = people[pid]["win_start"]
            win_e = people[pid]["win_end"]
            min_d = people[pid]["min"]
            implies_list.append(Implies(person[i] == pid, And(start[i] >= win_s,
                                                              end[i] <= win_e,
                                                              end[i] - start[i] >= min_d)))
        opt.add(Or(person[i] == 0, And(*implies_list)))

    # Contiguity: once a slot is empty, all following are empty
    for i in range(num_slots - 1):
        opt.add(Implies(person[i] == 0, person[i+1] == 0))

    # Uniqueness: no person appears more than once
    for i in range(num_slots):
        for j in range(i + 1, num_slots):
            opt.add(Or(person[i] == 0, person[j] == 0, person[i] != person[j]))

    # Travel time expressions
    def travel_from_start_expr(person_var):
        expr = IntVal(0)
        for pid in person_ids:
            expr = expr + If(person_var == pid, IntVal(travel_from_start[pid]), IntVal(0))
        return expr

    def travel_between_expr(prev_person_var, curr_person_var):
        expr = IntVal(0)
        for p in person_ids:
            for q in person_ids:
                expr = expr + If(And(prev_person_var == p, curr_person_var == q),
                                 IntVal(travel_matrix[(p, q)]), IntVal(0))
        return expr

    # First meeting travel from start
    opt.add(Implies(person[0] != 0, start[0] >= start_time + travel_from_start_expr(person[0])))

    # Consecutive meeting travel
    for i in range(1, num_slots):
        opt.add(Implies(And(person[i-1] != 0, person[i] != 0),
                        start[i] >= end[i-1] + travel_between_expr(person[i-1], person[i])))

    # Served booleans and objective: maximize number of friends met
    served = {pid: Bool(f"served_{pid}") for pid in person_ids}
    for pid in person_ids:
        opt.add(served[pid] == Or(*[person[i] == pid for i in range(num_slots)]))

    obj1 = Sum([If(served[pid], IntVal(1), IntVal(0)) for pid in person_ids])  # maximize number of friends met
    obj2 = Sum([If(person[i] != 0, end[i] - start[i], IntVal(0)) for i in range(num_slots)])  # maximize total meeting time

    opt.maximize(obj1)
    opt.maximize(obj2)

    result = opt.check()
    itinerary = []

    if result == sat:
        m = opt.model()
        for i in range(num_slots):
            pid = m.evaluate(person[i]).as_long()
            if pid == 0:
                continue
            s_i = m.evaluate(start[i]).as_long()
            e_i = m.evaluate(end[i]).as_long()
            entry = {
                "action": "meet",
                "location": person_to_location[pid],
                "person": people[pid]["name"],
                "start_time": fmt_time(s_i),
                "end_time": fmt_time(e_i)
            }
            itinerary.append(entry)
    else:
        itinerary = []

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()