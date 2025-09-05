import json
from z3 import Optimize, Int, Bool, Sum, If, And, Or, Not, Implies, is_true, sat

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations and travel times (in minutes), directional
    travel = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Nob Hill"): 7,

        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Nob Hill"): 8,

        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Mission District"): 18,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Nob Hill"): 8,

        ("Union Square", "North Beach"): 10,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Nob Hill"): 9,

        ("Mission District", "North Beach"): 17,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Nob Hill"): 12,

        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Nob Hill"): 20,

        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Golden Gate Park"): 17,
    }

    # People, availabilities, and minimum meeting durations (in minutes)
    people = {
        "James":   {"location": "Pacific Heights",  "start": 20*60,   "end": 22*60,   "min": 120},
        "Robert":  {"location": "Chinatown",        "start": 12*60+15,"end": 16*60+45,"min": 90},
        "Jeffrey": {"location": "Union Square",     "start": 9*60+30, "end": 15*60+30,"min": 120},
        "Carol":   {"location": "Mission District", "start": 18*60+15,"end": 21*60+15,"min": 15},
        "Mark":    {"location": "Golden Gate Park", "start": 11*60+30,"end": 17*60+45,"min": 15},
        "Sandra":  {"location": "Nob Hill",         "start": 8*60,    "end": 15*60+30,"min": 15},
    }

    start_location = "North Beach"
    arrival_time = 9*60  # 9:00

    names = list(people.keys())

    opt = Optimize()

    # Decision variables
    s = {p: Int(f"s_{p}") for p in names}
    e = {p: Int(f"e_{p}") for p in names}
    meet = {p: Bool(f"meet_{p}") for p in names}

    # Bounds and availability constraints
    for p in names:
        loc = people[p]["location"]
        avail_s = people[p]["start"]
        avail_e = people[p]["end"]
        min_d = people[p]["min"]
        # Time bounds
        opt.add(And(s[p] >= 0, s[p] <= 24*60))
        opt.add(And(e[p] >= 0, e[p] <= 24*60))
        # If meeting p, must be within availability and meet minimum duration
        opt.add(Implies(meet[p], s[p] >= avail_s))
        opt.add(Implies(meet[p], e[p] <= avail_e))
        opt.add(Implies(meet[p], e[p] - s[p] >= min_d))
        # If not meeting p, set times to 0 to keep model clean
        opt.add(Implies(Not(meet[p]), And(s[p] == 0, e[p] == 0)))
        # Account for travel from starting location to first possible meeting
        opt.add(Implies(meet[p], s[p] >= arrival_time + travel[(start_location, loc)]))

    # Non-overlap and travel-time constraints between meetings (disjunctive constraints)
    before = {}
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            p = names[i]
            q = names[j]
            before[(p, q)] = Bool(f"before_{p}_{q}")
            loc_p = people[p]["location"]
            loc_q = people[q]["location"]

            # If both meetings are scheduled, enforce ordering with travel time
            opt.add(Implies(
                And(meet[p], meet[q]),
                Or(
                    And(before[(p, q)], e[p] + travel[(loc_p, loc_q)] <= s[q]),
                    And(Not(before[(p, q)]), e[q] + travel[(loc_q, loc_p)] <= s[p])
                )
            ))

    # Objectives: maximize number of people met, then maximize total meeting time
    total_met = Sum([If(meet[p], 1, 0) for p in names])
    total_duration = Sum([If(meet[p], e[p] - s[p], 0) for p in names])

    opt.maximize(total_met)
    opt.maximize(total_duration)

    result = {"itinerary": []}

    if opt.check() == sat:
        m = opt.model()
        meetings = []
        for p in names:
            if is_true(m[meet[p]]):
                start_min = m[s[p]].as_long()
                end_min = m[e[p]].as_long()
                meetings.append({
                    "person": p,
                    "location": people[p]["location"],
                    "start": start_min,
                    "end": end_min
                })

        # Sort by start time
        meetings.sort(key=lambda x: x["start"])

        for item in meetings:
            result["itinerary"].append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": minutes_to_str(item["start"]),
                "end_time": minutes_to_str(item["end"])
            })
    else:
        # No feasible schedule
        result["itinerary"] = []

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()