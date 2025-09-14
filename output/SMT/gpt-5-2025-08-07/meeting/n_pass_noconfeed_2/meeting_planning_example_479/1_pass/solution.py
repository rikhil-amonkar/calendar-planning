import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    E = "Embarcadero"
    locations = [
        "Embarcadero",
        "Golden Gate Park",
        "Haight-Ashbury",
        "Bayview",
        "Presidio",
        "Financial District",
    ]

    # Travel times in minutes (directed)
    travel = {
        "Embarcadero": {
            "Embarcadero": 0,
            "Golden Gate Park": 25,
            "Haight-Ashbury": 21,
            "Bayview": 21,
            "Presidio": 20,
            "Financial District": 5,
        },
        "Golden Gate Park": {
            "Embarcadero": 25,
            "Golden Gate Park": 0,
            "Haight-Ashbury": 7,
            "Bayview": 23,
            "Presidio": 11,
            "Financial District": 26,
        },
        "Haight-Ashbury": {
            "Embarcadero": 20,
            "Golden Gate Park": 7,
            "Haight-Ashbury": 0,
            "Bayview": 18,
            "Presidio": 15,
            "Financial District": 21,
        },
        "Bayview": {
            "Embarcadero": 19,
            "Golden Gate Park": 22,
            "Haight-Ashbury": 19,
            "Bayview": 0,
            "Presidio": 31,
            "Financial District": 19,
        },
        "Presidio": {
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Haight-Ashbury": 15,
            "Bayview": 31,
            "Presidio": 0,
            "Financial District": 23,
        },
        "Financial District": {
            "Embarcadero": 4,
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Bayview": 19,
            "Presidio": 22,
            "Financial District": 0,
        },
    }

    # People and constraints
    people = [
        {"name": "Mary", "location": "Golden Gate Park", "avail_start": 8*60+45, "avail_end": 11*60+45, "min_duration": 45},
        {"name": "Kevin", "location": "Haight-Ashbury", "avail_start": 10*60+15, "avail_end": 16*60+15, "min_duration": 90},
        {"name": "Deborah", "location": "Bayview", "avail_start": 15*60, "avail_end": 19*60+15, "min_duration": 120},
        {"name": "Stephanie", "location": "Presidio", "avail_start": 10*60, "avail_end": 17*60+15, "min_duration": 120},
        {"name": "Emily", "location": "Financial District", "avail_start": 11*60+30, "avail_end": 21*60+45, "min_duration": 105},
    ]

    n = len(people)
    # Z3 variables
    attend = [Bool(f"attend_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    dur = [Int(f"dur_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]

    # Precedence booleans for all ordered pairs
    precedes = {}
    for i in range(n):
        for j in range(n):
            if i != j:
                precedes[(i, j)] = Bool(f"precedes_{i}_{j}")

    o = Optimize()
    o.set(priority='lex')

    # General constraints
    for i, p in enumerate(people):
        s_av, e_av, min_d = p["avail_start"], p["avail_end"], p["min_duration"]

        o.add(start[i] >= s_av)
        o.add(start[i] <= e_av)  # bound start to window for well-posedness
        o.add(dur[i] >= 0)
        o.add(end[i] == start[i] + dur[i])
        o.add(end[i] <= e_av)

        # If attending, ensure minimum duration; if not, duration is 0
        o.add(Implies(attend[i], dur[i] >= min_d))
        o.add(Implies(Not(attend[i]), dur[i] == 0))

    # Non-overlap and travel-time feasibility via pairwise precedence
    for i in range(n):
        for j in range(i + 1, n):
            pij = precedes[(i, j)]
            pji = precedes[(j, i)]
            li = people[i]["location"]
            lj = people[j]["location"]
            t_ij = travel[li][lj]
            t_ji = travel[lj][li]

            # If both attended, exactly one precedes the other; otherwise, neither precedence is active.
            both_attend = And(attend[i], attend[j])
            o.add(Implies(both_attend, Xor(pij, pji)))
            o.add(Implies(Not(both_attend), And(Not(pij), Not(pji))))

            # If i precedes j, ensure enough time for travel and no overlap
            o.add(Implies(pij, end[i] + t_ij <= start[j]))
            o.add(Implies(pji, end[j] + t_ji <= start[i]))

    # Reachability from starting location (Embarcadero at 9:00)
    day_start = 9 * 60  # 540
    for i, p in enumerate(people):
        conds = []
        # First in chain possibility: reachable from Embarcadero at day_start
        conds.append(start[i] >= day_start + travel[E][p["location"]])
        # Or has a predecessor who precedes i
        for j in range(n):
            if j != i:
                conds.append(And(attend[j], precedes[(j, i)]))
        o.add(Implies(attend[i], Or(conds)))

    # Objective 1: maximize number of attended meetings
    total_attended = Sum([If(attend[i], 1, 0) for i in range(n)])
    o.maximize(total_attended)

    # Objective 2: minimize end time of the last meeting to avoid unnecessary waiting/extension
    last_end = Int("last_end")
    o.add(last_end >= 0)
    for i in range(n):
        o.add(Implies(attend[i], last_end >= end[i]))
    o.minimize(last_end)

    # Solve
    result = o.check()
    itinerary = []
    if result == sat or result == unknown:
        m = o.model()
        schedule = []
        for i, p in enumerate(people):
            if is_true(m.eval(attend[i], model_completion=True)):
                s = m.eval(start[i], model_completion=True).as_long()
                e = m.eval(end[i], model_completion=True).as_long()
                schedule.append({
                    "person": p["name"],
                    "location": p["location"],
                    "start": s,
                    "end": e
                })
        # Sort by start time
        schedule.sort(key=lambda x: x["start"])
        for item in schedule:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": minutes_to_str(item["start"]),
                "end_time": minutes_to_str(item["end"])
            })
    else:
        # Unsat: return empty itinerary (should not happen with given data)
        itinerary = []

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()