import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Xor, sat

def minutes(h, m):
    return h * 60 + m

def to_24h_str(mins_since_9):
    total = 9 * 60 + mins_since_9
    h = total // 60
    m = total % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    RH = "Russian Hill"
    locations = [
        RH,
        "Sunset District",
        "Union Square",
        "Nob Hill",
        "Marina District",
        "Richmond District",
        "Financial District",
        "Embarcadero",
        "The Castro",
        "Alamo Square",
        "Presidio",
    ]

    # Travel times (minutes)
    T = {
        "Russian Hill": {
            "Sunset District": 23,
            "Union Square": 10,
            "Nob Hill": 5,
            "Marina District": 7,
            "Richmond District": 14,
            "Financial District": 11,
            "Embarcadero": 8,
            "The Castro": 21,
            "Alamo Square": 15,
            "Presidio": 14,
        },
        "Sunset District": {
            "Russian Hill": 24,
            "Union Square": 30,
            "Nob Hill": 27,
            "Marina District": 21,
            "Richmond District": 12,
            "Financial District": 30,
            "Embarcadero": 30,
            "The Castro": 17,
            "Alamo Square": 17,
            "Presidio": 16,
        },
        "Union Square": {
            "Russian Hill": 13,
            "Sunset District": 27,
            "Nob Hill": 9,
            "Marina District": 18,
            "Richmond District": 20,
            "Financial District": 9,
            "Embarcadero": 11,
            "The Castro": 17,
            "Alamo Square": 15,
            "Presidio": 24,
        },
        "Nob Hill": {
            "Russian Hill": 5,
            "Sunset District": 24,
            "Union Square": 7,
            "Marina District": 11,
            "Richmond District": 14,
            "Financial District": 9,
            "Embarcadero": 9,
            "The Castro": 17,
            "Alamo Square": 11,
            "Presidio": 17,
        },
        "Marina District": {
            "Russian Hill": 8,
            "Sunset District": 19,
            "Union Square": 16,
            "Nob Hill": 12,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 14,
            "The Castro": 22,
            "Alamo Square": 15,
            "Presidio": 10,
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Sunset District": 11,
            "Union Square": 21,
            "Nob Hill": 17,
            "Marina District": 9,
            "Financial District": 22,
            "Embarcadero": 19,
            "The Castro": 16,
            "Alamo Square": 13,
            "Presidio": 7,
        },
        "Financial District": {
            "Russian Hill": 11,
            "Sunset District": 30,
            "Union Square": 9,
            "Nob Hill": 8,
            "Marina District": 15,
            "Richmond District": 21,
            "Embarcadero": 4,
            "The Castro": 20,
            "Alamo Square": 17,
            "Presidio": 22,
        },
        "Embarcadero": {
            "Russian Hill": 8,
            "Sunset District": 30,
            "Union Square": 10,
            "Nob Hill": 10,
            "Marina District": 12,
            "Richmond District": 21,
            "Financial District": 5,
            "The Castro": 25,
            "Alamo Square": 19,
            "Presidio": 20,
        },
        "The Castro": {
            "Russian Hill": 18,
            "Sunset District": 17,
            "Union Square": 19,
            "Nob Hill": 16,
            "Marina District": 21,
            "Richmond District": 16,
            "Financial District": 21,
            "Embarcadero": 22,
            "Alamo Square": 8,
            "Presidio": 20,
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Sunset District": 16,
            "Union Square": 14,
            "Nob Hill": 11,
            "Marina District": 15,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 16,
            "The Castro": 8,
            "Presidio": 17,
        },
        "Presidio": {
            "Russian Hill": 14,
            "Sunset District": 15,
            "Union Square": 22,
            "Nob Hill": 18,
            "Marina District": 11,
            "Richmond District": 7,
            "Financial District": 23,
            "Embarcadero": 20,
            "The Castro": 21,
            "Alamo Square": 19,
        },
    }

    def travel(a, b):
        if a == b:
            return 0
        return T[a][b]

    # Day timeline baseline: start at 9:00 (540 minutes), end at 22:00 (1320 minutes)
    day_start = minutes(9, 0)
    day_end = minutes(22, 0)
    horizon = day_end - day_start  # 780 minutes

    # Friends and constraints
    people = [
        # name, location, availability start (24h), availability end (24h), min meeting duration
        ("David", "Sunset District", minutes(9, 15), minutes(22, 0), 15),
        ("Kenneth", "Union Square", minutes(21, 15), minutes(21, 45), 15),
        ("Patricia", "Nob Hill", minutes(15, 0), minutes(19, 15), 120),
        ("Mary", "Marina District", minutes(14, 45), minutes(16, 45), 45),
        ("Charles", "Richmond District", minutes(17, 15), minutes(21, 0), 15),
        ("Joshua", "Financial District", minutes(14, 30), minutes(17, 15), 90),
        ("Ronald", "Embarcadero", minutes(18, 15), minutes(20, 45), 30),
        ("George", "The Castro", minutes(14, 15), minutes(19, 0), 105),
        ("Kimberly", "Alamo Square", minutes(9, 0), minutes(14, 30), 105),
        ("William", "Presidio", minutes(7, 0), minutes(12, 45), 60),
    ]

    # Convert availability to minutes since 9:00
    persons = []
    for (name, loc, s_abs, e_abs, dmin) in people:
        s_rel = s_abs - day_start
        e_rel = e_abs - day_start
        # clamp end to the day horizon (cannot meet after 22:00)
        e_rel = min(e_rel, horizon)
        persons.append({
            "name": name,
            "location": loc,
            "start": s_rel,
            "end": e_rel,
            "min_dur": dmin
        })

    n = len(persons)

    opt = Optimize()

    start_vars = [Int(f"start_{i}") for i in range(n)]
    dur_vars = [Int(f"dur_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    sel_vars = [Bool(f"sel_{i}") for i in range(n)]

    # Basic bounds and availability constraints
    for i in range(n):
        pi = persons[i]
        s0 = max(0, pi["start"])  # cannot start before 9:00
        e1 = min(horizon, pi["end"])
        opt.add(start_vars[i] >= 0)
        opt.add(dur_vars[i] >= 0)
        opt.add(end_vars[i] == start_vars[i] + dur_vars[i])

        # If selected, enforce availability window and minimum duration
        opt.add(If(sel_vars[i],
                   And(start_vars[i] >= s0,
                       end_vars[i] <= e1,
                       dur_vars[i] >= pi["min_dur"],
                       # Must be able to arrive from the start location (Russian Hill) at 9:00
                       start_vars[i] >= travel(RH, pi["location"])
                       ),
                   And(dur_vars[i] == 0)))  # not selected => zero duration

    # Pairwise ordering and travel constraints
    before = [[None for _ in range(n)] for __ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            before[i][j] = Bool(f"before_{i}_{j}")

    for i in range(n):
        for j in range(i + 1, n):
            pij = persons[i]
            pji = persons[j]

            # If both selected, exactly one is before the other
            opt.add(Implies(And(sel_vars[i], sel_vars[j]),
                            Xor(before[i][j], before[j][i])))

            # If i before j, enforce travel time feasibility
            tij = travel(pij["location"], pji["location"])
            tji = travel(pji["location"], pij["location"])

            opt.add(Implies(And(sel_vars[i], sel_vars[j], before[i][j]),
                            start_vars[j] >= end_vars[i] + tij))
            opt.add(Implies(And(sel_vars[i], sel_vars[j], before[j][i]),
                            start_vars[i] >= end_vars[j] + tji))

    # Objective: maximize number of friends met; tie-breaker maximize total meeting time
    total_meetings = sum([If(sel_vars[i], 1, 0) for i in range(n)])
    total_duration = sum([dur_vars[i] for i in range(n)])
    opt.maximize(total_meetings)
    opt.maximize(total_duration)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract selected meetings and sort by start time
    schedule = []
    for i in range(n):
        if model.eval(sel_vars[i]).is_true():
            s = model.eval(start_vars[i]).as_long()
            e = model.eval(end_vars[i]).as_long()
            schedule.append((s, e, i))

    schedule.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, i in schedule:
        pi = persons[i]
        itinerary.append({
            "action": "meet",
            "location": pi["location"],
            "person": pi["name"],
            "start_time": to_24h_str(s),
            "end_time": to_24h_str(e),
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()