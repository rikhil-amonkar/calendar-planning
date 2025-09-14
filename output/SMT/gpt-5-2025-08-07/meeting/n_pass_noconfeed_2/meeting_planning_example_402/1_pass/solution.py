import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

def build_solver():
    # Locations
    GGP = "Golden Gate Park"
    locations = [
        "Golden Gate Park",
        "Haight-Ashbury",
        "Sunset District",
        "Marina District",
        "Financial District",
        "Union Square",
    ]

    # Travel times (in minutes)
    travel = {
        ( "Golden Gate Park", "Haight-Ashbury" ): 7,
        ( "Golden Gate Park", "Sunset District" ): 10,
        ( "Golden Gate Park", "Marina District" ): 16,
        ( "Golden Gate Park", "Financial District" ): 26,
        ( "Golden Gate Park", "Union Square" ): 22,

        ( "Haight-Ashbury", "Golden Gate Park" ): 7,
        ( "Haight-Ashbury", "Sunset District" ): 15,
        ( "Haight-Ashbury", "Marina District" ): 17,
        ( "Haight-Ashbury", "Financial District" ): 21,
        ( "Haight-Ashbury", "Union Square" ): 17,

        ( "Sunset District", "Golden Gate Park" ): 11,
        ( "Sunset District", "Haight-Ashbury" ): 15,
        ( "Sunset District", "Marina District" ): 21,
        ( "Sunset District", "Financial District" ): 30,
        ( "Sunset District", "Union Square" ): 30,

        ( "Marina District", "Golden Gate Park" ): 18,
        ( "Marina District", "Haight-Ashbury" ): 16,
        ( "Marina District", "Sunset District" ): 19,
        ( "Marina District", "Financial District" ): 17,
        ( "Marina District", "Union Square" ): 16,

        ( "Financial District", "Golden Gate Park" ): 23,
        ( "Financial District", "Haight-Ashbury" ): 19,
        ( "Financial District", "Sunset District" ): 31,
        ( "Financial District", "Marina District" ): 15,
        ( "Financial District", "Union Square" ): 9,

        ( "Union Square", "Golden Gate Park" ): 22,
        ( "Union Square", "Haight-Ashbury" ): 18,
        ( "Union Square", "Sunset District" ): 26,
        ( "Union Square", "Marina District" ): 18,
        ( "Union Square", "Financial District" ): 9,
    }

    def ttime(a, b):
        return travel[(a, b)]

    # Participants and constraints
    people = [
        {"name": "Sarah",   "location": "Haight-Ashbury",     "start": 17*60,      "end": 21*60 + 30, "min_dur": 105},
        {"name": "Patricia","location": "Sunset District",     "start": 17*60,      "end": 19*60 + 45, "min_dur": 45},
        {"name": "Matthew", "location": "Marina District",     "start": 9*60 + 15,  "end": 12*60,      "min_dur": 15},
        {"name": "Joseph",  "location": "Financial District",  "start": 14*60 + 15, "end": 18*60 + 45, "min_dur": 30},
        {"name": "Robert",  "location": "Union Square",        "start": 10*60 + 15, "end": 21*60 + 45, "min_dur": 15},
    ]

    start_location = GGP
    day_start = 9*60  # 9:00

    n = len(people)
    # Z3 variables
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start_time_vars = [Int(f"start_{i}") for i in range(n)]
    durations = [people[i]["min_dur"] for i in range(n)]

    opt = Optimize()

    # Domain constraints and availability windows
    for i in range(n):
        ws = people[i]["start"]
        we = people[i]["end"]
        d  = durations[i]
        loc = people[i]["location"]

        # Start time domain (within a reasonable day range)
        opt.add(And(start_time_vars[i] >= 0, start_time_vars[i] <= 24*60 + 59))

        # If meeting, it must fit in availability window
        opt.add(Implies(meet[i], And(start_time_vars[i] >= ws, start_time_vars[i] + d <= we)))

        # Must be reachable from the starting location at day start
        opt.add(Implies(meet[i], start_time_vars[i] >= day_start + ttime(start_location, loc)))

    # Pairwise sequencing constraints with travel times
    before = {}
    for i in range(n):
        for j in range(i+1, n):
            b_ij = Bool(f"before_{i}_{j}")  # True means i before j
            before[(i, j)] = b_ij
            ti = durations[i]
            tj = durations[j]
            li = people[i]["location"]
            lj = people[j]["location"]
            # If both meetings happen, enforce ordering with travel
            opt.add(Implies(And(meet[i], meet[j]),
                            Or(And(b_ij, start_time_vars[j] >= start_time_vars[i] + ti + ttime(li, lj)),
                               And(Not(b_ij), start_time_vars[i] >= start_time_vars[j] + tj + ttime(lj, li))))))

    # Objectives
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    # Secondary objective: finish earlier (minimize latest end among scheduled)
    last_end = Int("last_end")
    opt.add(last_end >= 0)
    for i in range(n):
        opt.add(Implies(meet[i], last_end >= start_time_vars[i] + durations[i]))
    opt.minimize(last_end)

    return opt, people, meet, start_time_vars, durations

def main():
    opt, people, meet, start_time_vars, durations = build_solver()
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return
    model = opt.model()

    itinerary = []
    for i in range(len(people)):
        m = model.evaluate(meet[i], model_completion=True)
        if is_true(m):
            s = model.evaluate(start_time_vars[i], model_completion=True).as_long()
            e = s + durations[i]
            itinerary.append({
                "action": "meet",
                "location": people[i]["location"],
                "person": people[i]["name"],
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e),
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()