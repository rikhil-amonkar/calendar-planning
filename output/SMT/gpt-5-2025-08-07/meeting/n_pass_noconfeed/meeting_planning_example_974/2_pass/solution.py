import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def time_to_minutes_24(s):
    # Not used, but helper if needed to parse times like '13:15'
    h, mm = map(int, s.split(":"))
    return h * 60 + mm

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    SUNSET = "Sunset District"
    locations = [
        "Sunset District",
        "Presidio",
        "Nob Hill",
        "Pacific Heights",
        "Mission District",
        "Marina District",
        "North Beach",
        "Russian Hill",
        "Richmond District",
        "Embarcadero",
        "Alamo Square"
    ]

    # Travel times (minutes), directional
    t = {}
    def set_t(frm, to, val):
        t[(frm, to)] = val

    # Input travel times
    set_t("Sunset District", "Presidio", 16)
    set_t("Sunset District", "Nob Hill", 27)
    set_t("Sunset District", "Pacific Heights", 21)
    set_t("Sunset District", "Mission District", 25)
    set_t("Sunset District", "Marina District", 21)
    set_t("Sunset District", "North Beach", 28)
    set_t("Sunset District", "Russian Hill", 24)
    set_t("Sunset District", "Richmond District", 12)
    set_t("Sunset District", "Embarcadero", 30)
    set_t("Sunset District", "Alamo Square", 17)

    set_t("Presidio", "Sunset District", 15)
    set_t("Presidio", "Nob Hill", 18)
    set_t("Presidio", "Pacific Heights", 11)
    set_t("Presidio", "Mission District", 26)
    set_t("Presidio", "Marina District", 11)
    set_t("Presidio", "North Beach", 18)
    set_t("Presidio", "Russian Hill", 14)
    set_t("Presidio", "Richmond District", 7)
    set_t("Presidio", "Embarcadero", 20)
    set_t("Presidio", "Alamo Square", 19)

    set_t("Nob Hill", "Sunset District", 24)
    set_t("Nob Hill", "Presidio", 17)
    set_t("Nob Hill", "Pacific Heights", 8)
    set_t("Nob Hill", "Mission District", 13)
    set_t("Nob Hill", "Marina District", 11)
    set_t("Nob Hill", "North Beach", 8)
    set_t("Nob Hill", "Russian Hill", 5)
    set_t("Nob Hill", "Richmond District", 14)
    set_t("Nob Hill", "Embarcadero", 9)
    set_t("Nob Hill", "Alamo Square", 11)

    set_t("Pacific Heights", "Sunset District", 21)
    set_t("Pacific Heights", "Presidio", 11)
    set_t("Pacific Heights", "Nob Hill", 8)
    set_t("Pacific Heights", "Mission District", 15)
    set_t("Pacific Heights", "Marina District", 6)
    set_t("Pacific Heights", "North Beach", 9)
    set_t("Pacific Heights", "Russian Hill", 7)
    set_t("Pacific Heights", "Richmond District", 12)
    set_t("Pacific Heights", "Embarcadero", 10)
    set_t("Pacific Heights", "Alamo Square", 10)

    set_t("Mission District", "Sunset District", 24)
    set_t("Mission District", "Presidio", 25)
    set_t("Mission District", "Nob Hill", 12)
    set_t("Mission District", "Pacific Heights", 16)
    set_t("Mission District", "Marina District", 19)
    set_t("Mission District", "North Beach", 17)
    set_t("Mission District", "Russian Hill", 15)
    set_t("Mission District", "Richmond District", 20)
    set_t("Mission District", "Embarcadero", 19)
    set_t("Mission District", "Alamo Square", 11)

    set_t("Marina District", "Sunset District", 19)
    set_t("Marina District", "Presidio", 10)
    set_t("Marina District", "Nob Hill", 12)
    set_t("Marina District", "Pacific Heights", 7)
    set_t("Marina District", "Mission District", 20)
    set_t("Marina District", "North Beach", 11)
    set_t("Marina District", "Russian Hill", 8)
    set_t("Marina District", "Richmond District", 11)
    set_t("Marina District", "Embarcadero", 14)
    set_t("Marina District", "Alamo Square", 15)

    set_t("North Beach", "Sunset District", 27)
    set_t("North Beach", "Presidio", 17)
    set_t("North Beach", "Nob Hill", 7)
    set_t("North Beach", "Pacific Heights", 8)
    set_t("North Beach", "Mission District", 18)
    set_t("North Beach", "Marina District", 9)
    set_t("North Beach", "Russian Hill", 4)
    set_t("North Beach", "Richmond District", 18)
    set_t("North Beach", "Embarcadero", 6)
    set_t("North Beach", "Alamo Square", 16)

    set_t("Russian Hill", "Sunset District", 23)
    set_t("Russian Hill", "Presidio", 14)
    set_t("Russian Hill", "Nob Hill", 5)
    set_t("Russian Hill", "Pacific Heights", 7)
    set_t("Russian Hill", "Mission District", 16)
    set_t("Russian Hill", "Marina District", 7)
    set_t("Russian Hill", "North Beach", 5)
    set_t("Russian Hill", "Richmond District", 14)
    set_t("Russian Hill", "Embarcadero", 8)
    set_t("Russian Hill", "Alamo Square", 15)

    set_t("Richmond District", "Sunset District", 11)
    set_t("Richmond District", "Presidio", 7)
    set_t("Richmond District", "Nob Hill", 17)
    set_t("Richmond District", "Pacific Heights", 10)
    set_t("Richmond District", "Mission District", 20)
    set_t("Richmond District", "Marina District", 9)
    set_t("Richmond District", "North Beach", 17)
    set_t("Richmond District", "Russian Hill", 13)
    set_t("Richmond District", "Embarcadero", 19)
    set_t("Richmond District", "Alamo Square", 13)

    set_t("Embarcadero", "Sunset District", 30)
    set_t("Embarcadero", "Presidio", 20)
    set_t("Embarcadero", "Nob Hill", 10)
    set_t("Embarcadero", "Pacific Heights", 11)
    set_t("Embarcadero", "Mission District", 20)
    set_t("Embarcadero", "Marina District", 12)
    set_t("Embarcadero", "North Beach", 5)
    set_t("Embarcadero", "Russian Hill", 8)
    set_t("Embarcadero", "Richmond District", 21)
    set_t("Embarcadero", "Alamo Square", 19)

    set_t("Alamo Square", "Sunset District", 16)
    set_t("Alamo Square", "Presidio", 17)
    set_t("Alamo Square", "Nob Hill", 11)
    set_t("Alamo Square", "Pacific Heights", 10)
    set_t("Alamo Square", "Mission District", 10)
    set_t("Alamo Square", "Marina District", 15)
    set_t("Alamo Square", "North Beach", 15)
    set_t("Alamo Square", "Russian Hill", 13)
    set_t("Alamo Square", "Richmond District", 11)
    set_t("Alamo Square", "Embarcadero", 16)

    # Ensure self-travel times are present to avoid KeyError
    for loc in locations:
        set_t(loc, loc, 0)

    # People and their constraints
    people = [
        {"name": "Charles",  "location": "Presidio",        "avail_start": minutes(13,15), "avail_end": minutes(15,0),  "min_dur": 105},
        {"name": "Robert",   "location": "Nob Hill",        "avail_start": minutes(13,15), "avail_end": minutes(17,30), "min_dur": 90},
        {"name": "Nancy",    "location": "Pacific Heights", "avail_start": minutes(14,45), "avail_end": minutes(22,0),  "min_dur": 105},
        {"name": "Brian",    "location": "Mission District","avail_start": minutes(15,30), "avail_end": minutes(22,0),  "min_dur": 60},
        {"name": "Kimberly", "location": "Marina District", "avail_start": minutes(17,0),  "avail_end": minutes(19,45), "min_dur": 75},
        {"name": "David",    "location": "North Beach",     "avail_start": minutes(14,45), "avail_end": minutes(16,30), "min_dur": 75},
        {"name": "William",  "location": "Russian Hill",    "avail_start": minutes(12,30), "avail_end": minutes(19,15), "min_dur": 120},
        {"name": "Jeffrey",  "location": "Richmond District","avail_start": minutes(12,0), "avail_end": minutes(19,15), "min_dur": 45},
        {"name": "Karen",    "location": "Embarcadero",     "avail_start": minutes(14,15), "avail_end": minutes(20,45), "min_dur": 60},
        {"name": "Joshua",   "location": "Alamo Square",    "avail_start": minutes(18,45), "avail_end": minutes(22,0),  "min_dur": 60},
    ]
    N = len(people)

    # Precompute travel matrix between people locations and from Sunset
    loc_of = [p["location"] for p in people]
    start_travel = []
    for k in range(N):
        start_travel.append(t[(SUNSET, loc_of[k])])

    t_pp = [[0]*N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            if i == j:
                t_pp[i][j] = 0
            else:
                t_pp[i][j] = t[(loc_of[i], loc_of[j])]

    # SMT model
    opt = Optimize()

    P = N  # maximum number of meeting slots
    person_at = [Int(f"person_at_{i}") for i in range(P)]
    used = [Bool(f"used_{i}") for i in range(P)]
    start = [Int(f"start_{i}") for i in range(P)]
    end = [Int(f"end_{i}") for i in range(P)]

    # Domains
    for i in range(P):
        opt.add(person_at[i] >= -1, person_at[i] < N)
        opt.add(used[i] == (person_at[i] >= 0))
        opt.add(start[i] >= 0, start[i] <= 24*60)
        opt.add(end[i] >= 0, end[i] <= 24*60)

    # Prefix property: no gaps (once unused, all later are unused)
    for i in range(P-1):
        opt.add(Or(Not(used[i+1]), used[i]))

    # No duplicate people across used positions
    for i in range(P):
        for j in range(i+1, P):
            opt.add(Or(person_at[i] == -1, person_at[j] == -1, person_at[i] != person_at[j]))

    # Helper functions to express travel time based on person indices (piecewise)
    def start_travel_expr(idx_expr):
        expr = IntVal(0)
        for b in range(N):
            expr = If(idx_expr == b, IntVal(start_travel[b]), expr)
        return expr

    def travel_between_expr(idx_from, idx_to):
        expr = IntVal(0)
        for a in range(N):
            for b in range(N):
                expr = If(And(idx_from == a, idx_to == b), IntVal(t_pp[a][b]), expr)
        return expr

    day_start = minutes(9,0)

    # Meeting constraints per slot and person
    for i in range(P):
        # Basic validity if used
        opt.add(Implies(used[i], end[i] > start[i]))
        # Availability and minimum duration depending on assigned person
        for k in range(N):
            p = people[k]
            opt.add(Implies(person_at[i] == k, And(
                start[i] >= p["avail_start"],
                end[i] <= p["avail_end"],
                end[i] - start[i] >= p["min_dur"]
            )))

    # Travel/time ordering constraints
    # First meeting: from Sunset at 9:00
    opt.add(Implies(used[0], start[0] >= day_start + start_travel_expr(person_at[0])))

    # Subsequent meetings: sequential with travel time
    for i in range(1, P):
        opt.add(Implies(used[i], start[i] >= end[i-1] + travel_between_expr(person_at[i-1], person_at[i])))

    # Meet flags and objective
    meet_flag = [Bool(f"meet_{k}") for k in range(N)]
    for k in range(N):
        opt.add(meet_flag[k] == Or([person_at[i] == k for i in range(P)]))

    total_meets = Sum([If(meet_flag[k], IntVal(1), IntVal(0)) for k in range(N)])
    total_meeting_minutes = Sum([If(used[i], end[i] - start[i], IntVal(0)) for i in range(P)])

    # Maximize number of meetings, then maximize total meeting time as a tiebreaker
    opt.maximize(total_meets)
    opt.maximize(total_meeting_minutes)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    m = opt.model()

    itinerary = []
    # Determine number of used slots (prefix)
    L = 0
    for i in range(P):
        if is_true(m.eval(used[i])):
            L = i + 1
        else:
            break

    for i in range(L):
        k = m.eval(person_at[i]).as_long()
        p = people[k]
        st = m.eval(start[i]).as_long()
        et = m.eval(end[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(st),
            "end_time": minutes_to_str(et)
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()