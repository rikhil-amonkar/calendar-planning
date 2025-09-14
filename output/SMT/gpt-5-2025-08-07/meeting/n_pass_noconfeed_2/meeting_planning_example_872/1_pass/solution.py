# SOLUTION:
import json
from z3 import Optimize, Int, Bool, If, And, Or, Sum, IntVal

def minutes(h, m):
    return h*60 + m

def parse_time_str(t):
    # not used; kept for completeness
    h, m = map(int, t.split(":"))
    return minutes(h, m)

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def build_travel_times():
    L = [
        "Presidio",
        "Haight-Ashbury",
        "Nob Hill",
        "Russian Hill",
        "North Beach",
        "Chinatown",
        "Union Square",
        "Embarcadero",
        "Financial District",
        "Marina District",
    ]
    t = {}
    def add(frm, to, mins):
        t[(frm, to)] = mins

    # Presidio
    add("Presidio", "Haight-Ashbury", 15)
    add("Presidio", "Nob Hill", 18)
    add("Presidio", "Russian Hill", 14)
    add("Presidio", "North Beach", 18)
    add("Presidio", "Chinatown", 21)
    add("Presidio", "Union Square", 22)
    add("Presidio", "Embarcadero", 20)
    add("Presidio", "Financial District", 23)
    add("Presidio", "Marina District", 11)

    # Haight-Ashbury
    add("Haight-Ashbury", "Presidio", 15)
    add("Haight-Ashbury", "Nob Hill", 15)
    add("Haight-Ashbury", "Russian Hill", 17)
    add("Haight-Ashbury", "North Beach", 19)
    add("Haight-Ashbury", "Chinatown", 19)
    add("Haight-Ashbury", "Union Square", 19)
    add("Haight-Ashbury", "Embarcadero", 20)
    add("Haight-Ashbury", "Financial District", 21)
    add("Haight-Ashbury", "Marina District", 17)

    # Nob Hill
    add("Nob Hill", "Presidio", 17)
    add("Nob Hill", "Haight-Ashbury", 13)
    add("Nob Hill", "Russian Hill", 5)
    add("Nob Hill", "North Beach", 8)
    add("Nob Hill", "Chinatown", 6)
    add("Nob Hill", "Union Square", 7)
    add("Nob Hill", "Embarcadero", 9)
    add("Nob Hill", "Financial District", 9)
    add("Nob Hill", "Marina District", 11)

    # Russian Hill
    add("Russian Hill", "Presidio", 14)
    add("Russian Hill", "Haight-Ashbury", 17)
    add("Russian Hill", "Nob Hill", 5)
    add("Russian Hill", "North Beach", 5)
    add("Russian Hill", "Chinatown", 9)
    add("Russian Hill", "Union Square", 10)
    add("Russian Hill", "Embarcadero", 8)
    add("Russian Hill", "Financial District", 11)
    add("Russian Hill", "Marina District", 7)

    # North Beach
    add("North Beach", "Presidio", 17)
    add("North Beach", "Haight-Ashbury", 18)
    add("North Beach", "Nob Hill", 7)
    add("North Beach", "Russian Hill", 4)
    add("North Beach", "Chinatown", 6)
    add("North Beach", "Union Square", 7)
    add("North Beach", "Embarcadero", 6)
    add("North Beach", "Financial District", 8)
    add("North Beach", "Marina District", 9)

    # Chinatown
    add("Chinatown", "Presidio", 19)
    add("Chinatown", "Haight-Ashbury", 19)
    add("Chinatown", "Nob Hill", 9)
    add("Chinatown", "Russian Hill", 7)
    add("Chinatown", "North Beach", 3)
    add("Chinatown", "Union Square", 7)
    add("Chinatown", "Embarcadero", 5)
    add("Chinatown", "Financial District", 5)
    add("Chinatown", "Marina District", 12)

    # Union Square
    add("Union Square", "Presidio", 24)
    add("Union Square", "Haight-Ashbury", 18)
    add("Union Square", "Nob Hill", 9)
    add("Union Square", "Russian Hill", 13)
    add("Union Square", "North Beach", 10)
    add("Union Square", "Chinatown", 7)
    add("Union Square", "Embarcadero", 11)
    add("Union Square", "Financial District", 9)
    add("Union Square", "Marina District", 18)

    # Embarcadero
    add("Embarcadero", "Presidio", 20)
    add("Embarcadero", "Haight-Ashbury", 21)
    add("Embarcadero", "Nob Hill", 10)
    add("Embarcadero", "Russian Hill", 8)
    add("Embarcadero", "North Beach", 5)
    add("Embarcadero", "Chinatown", 7)
    add("Embarcadero", "Union Square", 10)
    add("Embarcadero", "Financial District", 5)
    add("Embarcadero", "Marina District", 12)

    # Financial District
    add("Financial District", "Presidio", 22)
    add("Financial District", "Haight-Ashbury", 19)
    add("Financial District", "Nob Hill", 8)
    add("Financial District", "Russian Hill", 11)
    add("Financial District", "North Beach", 7)
    add("Financial District", "Chinatown", 5)
    add("Financial District", "Union Square", 9)
    add("Financial District", "Embarcadero", 4)
    add("Financial District", "Marina District", 15)

    # Marina District
    add("Marina District", "Presidio", 10)
    add("Marina District", "Haight-Ashbury", 16)
    add("Marina District", "Nob Hill", 12)
    add("Marina District", "Russian Hill", 8)
    add("Marina District", "North Beach", 11)
    add("Marina District", "Chinatown", 15)
    add("Marina District", "Union Square", 16)
    add("Marina District", "Embarcadero", 14)
    add("Marina District", "Financial District", 17)

    return t

def main():
    travel_times = build_travel_times()
    start_location = "Presidio"
    arrival_time = minutes(9, 0)

    people = [
        {"name": "Karen", "location": "Haight-Ashbury", "avail_start": minutes(21, 0), "avail_end": minutes(21, 45), "min_meet": 45},
        {"name": "Jessica", "location": "Nob Hill", "avail_start": minutes(13, 45), "avail_end": minutes(21, 0), "min_meet": 90},
        {"name": "Brian", "location": "Russian Hill", "avail_start": minutes(15, 30), "avail_end": minutes(21, 45), "min_meet": 60},
        {"name": "Kenneth", "location": "North Beach", "avail_start": minutes(9, 45), "avail_end": minutes(21, 0), "min_meet": 30},
        {"name": "Jason", "location": "Chinatown", "avail_start": minutes(8, 15), "avail_end": minutes(11, 45), "min_meet": 75},
        {"name": "Stephanie", "location": "Union Square", "avail_start": minutes(14, 45), "avail_end": minutes(18, 45), "min_meet": 105},
        {"name": "Kimberly", "location": "Embarcadero", "avail_start": minutes(9, 45), "avail_end": minutes(19, 30), "min_meet": 75},
        {"name": "Steven", "location": "Financial District", "avail_start": minutes(7, 15), "avail_end": minutes(21, 15), "min_meet": 60},
        {"name": "Mark", "location": "Marina District", "avail_start": minutes(10, 15), "avail_end": minutes(13, 0), "min_meet": 75},
    ]

    n_people = len(people)
    locations = [p["location"] for p in people]

    # Z3 variables
    slots = n_people  # up to one meeting per person
    start_vars = [Int(f"start_{i}") for i in range(slots)]
    end_vars = [Int(f"end_{i}") for i in range(slots)]
    person_vars = [Int(f"person_{i}") for i in range(slots)]  # -1 means unused, else index 0..n_people-1
    used_vars = [Bool(f"used_{i}") for i in range(slots)]

    opt = Optimize()

    # Domains and linkage
    for i in range(slots):
        opt.add(start_vars[i] >= 0, start_vars[i] <= 24*60)
        opt.add(end_vars[i] >= 0, end_vars[i] <= 24*60)
        opt.add(Or(person_vars[i] == -1, And(person_vars[i] >= 0, person_vars[i] < n_people)))
        opt.add(used_vars[i] == (person_vars[i] != -1))
        # If unused, zero out times for cleanliness
        opt.add(If(used_vars[i], end_vars[i] > start_vars[i], And(start_vars[i] == 0, end_vars[i] == 0)))

    # Prefix property: if a later slot is used, all previous are used
    for i in range(1, slots):
        opt.add(If(used_vars[i], used_vars[i-1], True))

    # Meeting constraints tied to selected person
    for i in range(slots):
        for p_idx, p in enumerate(people):
            opt.add(
                If(
                    person_vars[i] == p_idx,
                    And(
                        start_vars[i] >= p["avail_start"],
                        end_vars[i] <= p["avail_end"],
                        end_vars[i] - start_vars[i] >= p["min_meet"]
                    ),
                    True
                )
            )

    # Each person can be met at most once
    for p_idx in range(n_people):
        opt.add(Sum([If(person_vars[i] == p_idx, 1, 0) for i in range(slots)]) <= 1)

    # Travel constraints between consecutive used slots
    def travel_expr(idx_from, idx_to):
        # Sum over all (i,j) pairs to pick the right travel time
        terms = []
        for i in range(n_people):
            for j in range(n_people):
                frm = people[i]["location"]
                to = people[j]["location"]
                tt = travel_times[(frm, to)]
                terms.append(If(And(person_vars[idx_from] == i, person_vars[idx_to] == j), IntVal(tt), IntVal(0)))
        return Sum(terms)

    for i in range(slots - 1):
        opt.add(
            If(
                And(used_vars[i], used_vars[i+1]),
                start_vars[i+1] >= end_vars[i] + travel_expr(i, i+1),
                True
            )
        )

    # Initial travel from starting location and time to first meeting
    initial_travel_terms = []
    for i in range(n_people):
        tt = travel_times[(start_location, people[i]["location"])]
        initial_travel_terms.append(If(person_vars[0] == i, IntVal(tt), IntVal(0)))
    initial_travel = Sum(initial_travel_terms)
    opt.add(If(used_vars[0], start_vars[0] >= arrival_time + initial_travel, True))

    # Objective: maximize number of meetings
    total_meetings = Sum([If(used_vars[i], 1, 0) for i in range(slots)])
    opt.maximize(total_meetings)

    # Optional secondary objective: maximize total meeting time
    total_meeting_minutes = Sum([If(used_vars[i], end_vars[i] - start_vars[i], 0) for i in range(slots)])
    opt.maximize(total_meeting_minutes)

    if opt.check() != 1:
        # Fallback empty itinerary
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = opt.model()

    itinerary = []
    for i in range(slots):
        if m.evaluate(used_vars[i]).is_true():
            p_idx = m.evaluate(person_vars[i]).as_long()
            p = people[p_idx]
            st = m.evaluate(start_vars[i]).as_long()
            et = m.evaluate(end_vars[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": fmt_time(st),
                "end_time": fmt_time(et)
            })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()