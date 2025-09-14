import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    locations = [
        "Bayview",
        "North Beach",
        "Fisherman's Wharf",
        "Haight-Ashbury",
        "Nob Hill",
        "Golden Gate Park",
        "Union Square",
        "Alamo Square",
        "Presidio",
        "Chinatown",
        "Pacific Heights",
    ]

    # Travel times (minutes), directed
    T = {loc: {} for loc in locations}
    def add(a, b, t):
        T[a][b] = t

    # Bayview
    add("Bayview", "North Beach", 22)
    add("Bayview", "Fisherman's Wharf", 25)
    add("Bayview", "Haight-Ashbury", 19)
    add("Bayview", "Nob Hill", 20)
    add("Bayview", "Golden Gate Park", 22)
    add("Bayview", "Union Square", 18)
    add("Bayview", "Alamo Square", 16)
    add("Bayview", "Presidio", 32)
    add("Bayview", "Chinatown", 19)
    add("Bayview", "Pacific Heights", 23)
    # North Beach
    add("North Beach", "Bayview", 25)
    add("North Beach", "Fisherman's Wharf", 5)
    add("North Beach", "Haight-Ashbury", 18)
    add("North Beach", "Nob Hill", 7)
    add("North Beach", "Golden Gate Park", 22)
    add("North Beach", "Union Square", 7)
    add("North Beach", "Alamo Square", 16)
    add("North Beach", "Presidio", 17)
    add("North Beach", "Chinatown", 6)
    add("North Beach", "Pacific Heights", 8)
    # Fisherman's Wharf
    add("Fisherman's Wharf", "Bayview", 26)
    add("Fisherman's Wharf", "North Beach", 6)
    add("Fisherman's Wharf", "Haight-Ashbury", 22)
    add("Fisherman's Wharf", "Nob Hill", 11)
    add("Fisherman's Wharf", "Golden Gate Park", 25)
    add("Fisherman's Wharf", "Union Square", 13)
    add("Fisherman's Wharf", "Alamo Square", 21)
    add("Fisherman's Wharf", "Presidio", 17)
    add("Fisherman's Wharf", "Chinatown", 12)
    add("Fisherman's Wharf", "Pacific Heights", 12)
    # Haight-Ashbury
    add("Haight-Ashbury", "Bayview", 18)
    add("Haight-Ashbury", "North Beach", 19)
    add("Haight-Ashbury", "Fisherman's Wharf", 23)
    add("Haight-Ashbury", "Nob Hill", 15)
    add("Haight-Ashbury", "Golden Gate Park", 7)
    add("Haight-Ashbury", "Union Square", 19)
    add("Haight-Ashbury", "Alamo Square", 5)
    add("Haight-Ashbury", "Presidio", 15)
    add("Haight-Ashbury", "Chinatown", 19)
    add("Haight-Ashbury", "Pacific Heights", 12)
    # Nob Hill
    add("Nob Hill", "Bayview", 19)
    add("Nob Hill", "North Beach", 8)
    add("Nob Hill", "Fisherman's Wharf", 10)
    add("Nob Hill", "Haight-Ashbury", 13)
    add("Nob Hill", "Golden Gate Park", 17)
    add("Nob Hill", "Union Square", 7)
    add("Nob Hill", "Alamo Square", 11)
    add("Nob Hill", "Presidio", 17)
    add("Nob Hill", "Chinatown", 6)
    add("Nob Hill", "Pacific Heights", 8)
    # Golden Gate Park
    add("Golden Gate Park", "Bayview", 23)
    add("Golden Gate Park", "North Beach", 23)
    add("Golden Gate Park", "Fisherman's Wharf", 24)
    add("Golden Gate Park", "Haight-Ashbury", 7)
    add("Golden Gate Park", "Nob Hill", 20)
    add("Golden Gate Park", "Union Square", 22)
    add("Golden Gate Park", "Alamo Square", 9)
    add("Golden Gate Park", "Presidio", 11)
    add("Golden Gate Park", "Chinatown", 23)
    add("Golden Gate Park", "Pacific Heights", 16)
    # Union Square
    add("Union Square", "Bayview", 15)
    add("Union Square", "North Beach", 10)
    add("Union Square", "Fisherman's Wharf", 15)
    add("Union Square", "Haight-Ashbury", 18)
    add("Union Square", "Nob Hill", 9)
    add("Union Square", "Golden Gate Park", 22)
    add("Union Square", "Alamo Square", 15)
    add("Union Square", "Presidio", 24)
    add("Union Square", "Chinatown", 7)
    add("Union Square", "Pacific Heights", 15)
    # Alamo Square
    add("Alamo Square", "Bayview", 16)
    add("Alamo Square", "North Beach", 15)
    add("Alamo Square", "Fisherman's Wharf", 19)
    add("Alamo Square", "Haight-Ashbury", 5)
    add("Alamo Square", "Nob Hill", 11)
    add("Alamo Square", "Golden Gate Park", 9)
    add("Alamo Square", "Union Square", 14)
    add("Alamo Square", "Presidio", 17)
    add("Alamo Square", "Chinatown", 15)
    add("Alamo Square", "Pacific Heights", 10)
    # Presidio
    add("Presidio", "Bayview", 31)
    add("Presidio", "North Beach", 18)
    add("Presidio", "Fisherman's Wharf", 19)
    add("Presidio", "Haight-Ashbury", 15)
    add("Presidio", "Nob Hill", 18)
    add("Presidio", "Golden Gate Park", 12)
    add("Presidio", "Union Square", 22)
    add("Presidio", "Alamo Square", 19)
    add("Presidio", "Chinatown", 21)
    add("Presidio", "Pacific Heights", 11)
    # Chinatown
    add("Chinatown", "Bayview", 20)
    add("Chinatown", "North Beach", 3)
    add("Chinatown", "Fisherman's Wharf", 8)
    add("Chinatown", "Haight-Ashbury", 19)
    add("Chinatown", "Nob Hill", 9)
    add("Chinatown", "Golden Gate Park", 23)
    add("Chinatown", "Union Square", 7)
    add("Chinatown", "Alamo Square", 17)
    add("Chinatown", "Presidio", 19)
    add("Chinatown", "Pacific Heights", 10)
    # Pacific Heights
    add("Pacific Heights", "Bayview", 22)
    add("Pacific Heights", "North Beach", 9)
    add("Pacific Heights", "Fisherman's Wharf", 13)
    add("Pacific Heights", "Haight-Ashbury", 11)
    add("Pacific Heights", "Nob Hill", 8)
    add("Pacific Heights", "Golden Gate Park", 15)
    add("Pacific Heights", "Union Square", 12)
    add("Pacific Heights", "Alamo Square", 10)
    add("Pacific Heights", "Presidio", 11)
    add("Pacific Heights", "Chinatown", 11)

    # People and constraints
    people = [
        # name, location, availability start, availability end, minimum duration
        ("Brian", "North Beach", minutes(13,0), minutes(19,0), 90),
        ("Richard", "Fisherman's Wharf", minutes(11,0), minutes(12,45), 60),
        ("Ashley", "Haight-Ashbury", minutes(15,0), minutes(20,30), 90),
        ("Elizabeth", "Nob Hill", minutes(11,45), minutes(18,30), 75),
        ("Jessica", "Golden Gate Park", minutes(20,0), minutes(21,45), 105),
        ("Deborah", "Union Square", minutes(17,30), minutes(22,0), 60),
        ("Kimberly", "Alamo Square", minutes(17,30), minutes(21,15), 45),
        ("Matthew", "Presidio", minutes(8,15), minutes(9,0), 15),
        ("Kenneth", "Chinatown", minutes(13,45), minutes(19,30), 105),
        ("Anthony", "Pacific Heights", minutes(14,15), minutes(16,0), 30),
    ]

    n = len(people)
    start_loc = "Bayview"
    start_time = minutes(9, 0)

    opt = Optimize()

    # Decision variables
    s_vars = []
    e_vars = []
    m_vars = []
    f_vars = []

    for i in range(n):
        s = Int(f"s_{i}")
        e = Int(f"e_{i}")
        m = Bool(f"m_{i}")
        f = Bool(f"first_{i}")
        s_vars.append(s)
        e_vars.append(e)
        m_vars.append(m)
        f_vars.append(f)

        # Basic bounds
        opt.add(s >= 0, e >= 0, s <= 24*60, e <= 24*60)
        # If meeting, enforce within availability and min duration
        avail_s, avail_e = people[i][2], people[i][3]
        min_dur = people[i][4]
        opt.add(Implies(m, And(s >= avail_s, e <= avail_e, e - s >= min_dur)))
        # If not meeting, zero times and not first
        opt.add(Implies(Not(m), And(s == 0, e == 0, Not(f))))
        # First implies meeting
        opt.add(Implies(f, m))

    # Pairwise ordering and travel constraints
    o_vars = {}  # (i,j) with i<j => Bool means i before j
    for i in range(n):
        for j in range(i+1, n):
            o = Bool(f"o_{i}_{j}")
            o_vars[(i, j)] = o
            loc_i = people[i][1]
            loc_j = people[j][1]
            t_ij = T[loc_i][loc_j]
            t_ji = T[loc_j][loc_i]
            # Only relevant if both meetings occur
            both = And(m_vars[i], m_vars[j])
            opt.add(Implies(both, Or(
                And(o, e_vars[i] + t_ij <= s_vars[j]),
                And(Not(o), e_vars[j] + t_ji <= s_vars[i])
            )))
            # If not both, ordering var is irrelevant; no constraint needed.

    # Helper to express "i before j"
    def before_expr(i, j):
        if i < j:
            return o_vars[(i, j)]
        else:
            return Not(o_vars[(j, i)])

    # Exactly one "first" among those met (if any)
    sum_meet = Sum([If(m_vars[i], 1, 0) for i in range(n)])
    sum_first = Sum([If(f_vars[i], 1, 0) for i in range(n)])
    opt.add(sum_first <= sum_meet)
    opt.add(Or(sum_meet == 0, sum_first == 1))

    # First event must be reachable from start
    for i in range(n):
        loc_i = people[i][1]
        opt.add(Implies(f_vars[i], s_vars[i] >= start_time + T[start_loc][loc_i]))
        # If i is first and j is also met (j != i), i must be before j
        for j in range(n):
            if i == j:
                continue
            opt.add(Implies(And(f_vars[i], m_vars[j]), before_expr(i, j)))

    # Objectives: maximize number of meetings, then maximize total meeting time
    total_minutes = Sum([If(m_vars[i], e_vars[i] - s_vars[i], 0) for i in range(n)])
    opt.maximize(sum_meet)
    opt.maximize(total_minutes)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract chosen meetings
    meetings = []
    for i in range(n):
        if is_true(model[m_vars[i]]):
            s_val = model[s_vars[i]].as_long()
            e_val = model[e_vars[i]].as_long()
            meetings.append({
                "idx": i,
                "person": people[i][0],
                "location": people[i][1],
                "start": s_val,
                "end": e_val
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    itinerary = []
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "location": mt["location"],
            "person": mt["person"],
            "start_time": fmt_time(mt["start"]),
            "end_time": fmt_time(mt["end"]),
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    # The output must start with 'SOLUTION:' per instructions
    print("SOLUTION:")
    main()