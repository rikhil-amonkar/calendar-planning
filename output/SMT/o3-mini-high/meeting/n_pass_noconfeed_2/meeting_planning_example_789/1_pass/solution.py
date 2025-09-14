from z3 import *
import json

def minutes_to_timestr(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Friend meeting data
    # Times are represented in minutes since midnight.
    # Availability: avail_start, avail_end; minimum meeting duration: min_dur.
    friends = [
        {"name": "Betty",   "location": "Russian Hill",   "avail_start": 420,  "avail_end": 1005, "min_dur": 105},
        {"name": "Melissa", "location": "Alamo Square",   "avail_start": 570,  "avail_end": 1035, "min_dur": 105},
        {"name": "Joshua",  "location": "Haight-Ashbury", "avail_start": 735,  "avail_end": 1140, "min_dur": 90},
        {"name": "Jeffrey", "location": "Marina District","avail_start": 735,  "avail_end": 1080, "min_dur": 45},
        {"name": "James",   "location": "Bayview",        "avail_start": 450,  "avail_end": 1200, "min_dur": 90},
        {"name": "Anthony", "location": "Chinatown",      "avail_start": 705,  "avail_end": 810,  "min_dur": 75},
        {"name": "Timothy", "location": "Presidio",       "avail_start": 750,  "avail_end": 885,  "min_dur": 90},
        {"name": "Emily",   "location": "Sunset District", "avail_start": 1170, "avail_end": 1290, "min_dur": 120},
    ]
    n = len(friends)

    # Travel times in minutes between locations (asymmetric in general)
    travel = {}
    # From Union Square
    travel[("Union Square", "Russian Hill")]   = 13
    travel[("Union Square", "Alamo Square")]     = 15
    travel[("Union Square", "Haight-Ashbury")]     = 18
    travel[("Union Square", "Marina District")]    = 18
    travel[("Union Square", "Bayview")]            = 15
    travel[("Union Square", "Chinatown")]          = 7
    travel[("Union Square", "Presidio")]           = 24
    travel[("Union Square", "Sunset District")]      = 27

    # Russian Hill
    travel[("Russian Hill", "Union Square")]    = 10
    travel[("Russian Hill", "Alamo Square")]      = 15
    travel[("Russian Hill", "Haight-Ashbury")]      = 17
    travel[("Russian Hill", "Marina District")]     = 7
    travel[("Russian Hill", "Bayview")]            = 23
    travel[("Russian Hill", "Chinatown")]          = 9
    travel[("Russian Hill", "Presidio")]           = 14
    travel[("Russian Hill", "Sunset District")]      = 23

    # Alamo Square
    travel[("Alamo Square", "Union Square")]      = 14
    travel[("Alamo Square", "Russian Hill")]        = 13
    travel[("Alamo Square", "Haight-Ashbury")]        = 5
    travel[("Alamo Square", "Marina District")]       = 15
    travel[("Alamo Square", "Bayview")]             = 16
    travel[("Alamo Square", "Chinatown")]           = 15
    travel[("Alamo Square", "Presidio")]            = 17
    travel[("Alamo Square", "Sunset District")]       = 16

    # Haight-Ashbury
    travel[("Haight-Ashbury", "Union Square")]     = 19
    travel[("Haight-Ashbury", "Russian Hill")]       = 17
    travel[("Haight-Ashbury", "Alamo Square")]         = 5
    travel[("Haight-Ashbury", "Marina District")]      = 17
    travel[("Haight-Ashbury", "Bayview")]            = 18
    travel[("Haight-Ashbury", "Chinatown")]          = 19
    travel[("Haight-Ashbury", "Presidio")]           = 15
    travel[("Haight-Ashbury", "Sunset District")]      = 15

    # Marina District
    travel[("Marina District", "Union Square")]   = 16
    travel[("Marina District", "Russian Hill")]     = 8
    travel[("Marina District", "Alamo Square")]       = 15
    travel[("Marina District", "Haight-Ashbury")]      = 16
    travel[("Marina District", "Bayview")]          = 27
    travel[("Marina District", "Chinatown")]        = 15
    travel[("Marina District", "Presidio")]         = 10
    travel[("Marina District", "Sunset District")]    = 19

    # Bayview
    travel[("Bayview", "Union Square")]           = 18
    travel[("Bayview", "Russian Hill")]             = 23
    travel[("Bayview", "Alamo Square")]             = 16
    travel[("Bayview", "Haight-Ashbury")]           = 19
    travel[("Bayview", "Marina District")]          = 27
    travel[("Bayview", "Chinatown")]                = 19
    travel[("Bayview", "Presidio")]                 = 32
    travel[("Bayview", "Sunset District")]           = 23

    # Chinatown
    travel[("Chinatown", "Union Square")]           = 7
    travel[("Chinatown", "Russian Hill")]             = 7
    travel[("Chinatown", "Alamo Square")]            = 17
    travel[("Chinatown", "Haight-Ashbury")]           = 19
    travel[("Chinatown", "Marina District")]          = 12
    travel[("Chinatown", "Bayview")]                = 20
    travel[("Chinatown", "Presidio")]               = 19
    travel[("Chinatown", "Sunset District")]          = 29

    # Presidio
    travel[("Presidio", "Union Square")]            = 22
    travel[("Presidio", "Russian Hill")]              = 14
    travel[("Presidio", "Alamo Square")]              = 19
    travel[("Presidio", "Haight-Ashbury")]            = 15
    travel[("Presidio", "Marina District")]           = 11
    travel[("Presidio", "Bayview")]                 = 31
    travel[("Presidio", "Chinatown")]               = 21
    travel[("Presidio", "Sunset District")]          = 15

    # Sunset District
    travel[("Sunset District", "Union Square")]       = 30
    travel[("Sunset District", "Russian Hill")]         = 24
    travel[("Sunset District", "Alamo Square")]         = 17
    travel[("Sunset District", "Haight-Ashbury")]       = 15
    travel[("Sunset District", "Marina District")]      = 21
    travel[("Sunset District", "Bayview")]            = 22
    travel[("Sunset District", "Chinatown")]          = 30
    travel[("Sunset District", "Presidio")]           = 16

    # Initialize the optimizer
    opt = Optimize()

    # Decision variables:
    # m_vars[i] indicates whether meeting with friend i is scheduled.
    # s_vars[i] and e_vars[i] are start and end times for the meeting.
    m_vars = [Bool(f"m_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]

    # Binary ordering variables: before[(i, j)] is True if meeting i occurs before meeting j.
    before = {}
    for i in range(n):
        for j in range(n):
            if i != j:
                before[(i, j)] = Bool(f"before_{i}_{j}")

    # Meeting time constraints: if a meeting is scheduled, it must occur within the friend's availability window
    # and last at least the minimum duration.
    for i, friend in enumerate(friends):
        opt.add(Implies(m_vars[i], s_vars[i] >= friend["avail_start"]))
        opt.add(Implies(m_vars[i], e_vars[i] <= friend["avail_end"]))
        opt.add(Implies(m_vars[i], e_vars[i] - s_vars[i] >= friend["min_dur"]))

    # For every pair of meetings (i, j), if both are scheduled, enforce a strict ordering.
    # That is, exactly one of before[(i,j)] and before[(j,i)] is True.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(m_vars[i], m_vars[j]), before[(i, j)] == Not(before[(j, i)])))
            opt.add(Implies(And(m_vars[i], m_vars[j]), Or(before[(i, j)], before[(j, i)])))

    # Travel constraints: if meeting i is scheduled before meeting j then the start time of j must be at least
    # the end time of i plus the travel time from friend i's location to friend j's location.
    for i in range(n):
        for j in range(n):
            if i != j:
                tt = travel[(friends[i]["location"], friends[j]["location"])]
                opt.add(Implies(And(m_vars[i], m_vars[j], before[(i, j)]),
                                  s_vars[j] >= e_vars[i] + tt))

    # Transitivity: for any three distinct meetings (i, j, k), if i is before j and j is before k then i is before k.
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if i != j and j != k and i != k:
                    opt.add(Implies(And(m_vars[i], m_vars[j], m_vars[k],
                                        before[(i, j)], before[(j, k)]),
                                    before[(i, k)]))

    # The first meeting (i.e. one with no other meeting scheduled before it) must be reachable from Union Square.
    # You arrive at Union Square at 9:00 (540 minutes).
    for i in range(n):
        first_condition = And([Implies(m_vars[j], Not(before[(j, i)])) for j in range(n) if j != i])
        opt.add(Implies(And(m_vars[i], first_condition),
                        s_vars[i] >= 540 + travel[("Union Square", friends[i]["location"])]))

    # Objective: maximize the total number of meetings scheduled.
    total_meetings = Sum([If(m_vars[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i, friend in enumerate(friends):
            if is_true(model.evaluate(m_vars[i])):
                start_time = model.evaluate(s_vars[i]).as_long()
                end_time = model.evaluate(e_vars[i]).as_long()
                scheduled.append({
                    "person": friend["name"],
                    "location": friend["location"],
                    "start": start_time,
                    "end": end_time
                })
        # Sort meetings by their start time.
        scheduled.sort(key=lambda x: x["start"])
        itinerary = []
        for meet in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_timestr(meet["start"]),
                "end_time": minutes_to_timestr(meet["end"])
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()