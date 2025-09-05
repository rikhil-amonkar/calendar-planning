import json
from z3 import *

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Define friends with their meeting constraints
    # Times in minutes from midnight
    # 9:00 AM = 540, etc.
    friends = [
        {"name": "Mark", "location": "Marina District", "avail_start": 18*60+45, "avail_end": 21*60, "min_duration": 90},
        {"name": "Karen", "location": "Financial District", "avail_start": 9*60+30, "avail_end": 12*60+45, "min_duration": 90},
        {"name": "Barbara", "location": "Alamo Square", "avail_start": 10*60, "avail_end": 19*60+30, "min_duration": 90},
        {"name": "Nancy", "location": "Golden Gate Park", "avail_start": 16*60+45, "avail_end": 20*60, "min_duration": 105},
        {"name": "David", "location": "The Castro", "avail_start": 9*60, "avail_end": 18*60, "min_duration": 120},
        {"name": "Linda", "location": "Bayview", "avail_start": 18*60+15, "avail_end": 19*60+45, "min_duration": 45},
        {"name": "Kevin", "location": "Sunset District", "avail_start": 10*60, "avail_end": 17*60+45, "min_duration": 120},
        {"name": "Matthew", "location": "Haight-Ashbury", "avail_start": 10*60+15, "avail_end": 15*60+30, "min_duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "avail_start": 11*60+45, "avail_end": 16*60+45, "min_duration": 105}
    ]

    # Define travel times in minutes between locations (as given, note asymmetry)
    travel_times = {
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Nob Hill"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Nob Hill"): 16,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Nob Hill"): 27,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Haight-Ashbury"): 13
    }

    n = len(friends)
    opt = Optimize()

    # Decision variables:
    # x[i]: whether to meet friend i (True/False)
    # s[i], e[i]: start and end times for the meeting (in minutes from midnight)
    x_vars = [Bool(f"x_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]

    # For proper ordering of the day, we will enforce that any two scheduled meetings
    # do not overlap and have enough travel time between them.
    for i in range(n):
        friend = friends[i]
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_dur = friend["min_duration"]
        # If meeting is scheduled, enforce its time window and duration constraints
        opt.add(Implies(x_vars[i], s_vars[i] >= avail_start))
        opt.add(Implies(x_vars[i], e_vars[i] <= avail_end))
        opt.add(Implies(x_vars[i], e_vars[i] >= s_vars[i] + min_dur))
        # For non-scheduled meetings, fix start and end times to 0 (unused)
        opt.add(Implies(Not(x_vars[i]), s_vars[i] == 0))
        opt.add(Implies(Not(x_vars[i]), e_vars[i] == 0))
        opt.add(s_vars[i] >= 0)
        opt.add(e_vars[i] >= 0)

    # Enforce non-overlap with travel constraints between any two scheduled meetings.
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_i_j = travel_times[(loc_i, loc_j)]
            travel_j_i = travel_times[(loc_j, loc_i)]
            # If both meetings are scheduled then either i is before j or vice versa.
            opt.add(Implies(And(x_vars[i], x_vars[j]),
                Or(s_vars[i] >= e_vars[j] + travel_j_i,
                   s_vars[j] >= e_vars[i] + travel_i_j)))

    # Introduce a helper variable first_idx to indicate which meeting is the earliest (first to attend)
    first_idx = Int("first_idx")
    total_meetings = Sum([If(x_vars[i], 1, 0) for i in range(n)])
    
    # Create expressions to extract the start time and travel time for the meeting indicated by first_idx.
    s_first = If(first_idx == 0, s_vars[0],
             If(first_idx == 1, s_vars[1],
             If(first_idx == 2, s_vars[2],
             If(first_idx == 3, s_vars[3],
             If(first_idx == 4, s_vars[4],
             If(first_idx == 5, s_vars[5],
             If(first_idx == 6, s_vars[6],
             If(first_idx == 7, s_vars[7],
             If(first_idx == 8, s_vars[8],
             0)))))))))
    
    travel_from_RH = If(first_idx == 0, travel_times[("Russian Hill", friends[0]["location"])],
                     If(first_idx == 1, travel_times[("Russian Hill", friends[1]["location"])],
                     If(first_idx == 2, travel_times[("Russian Hill", friends[2]["location"])],
                     If(first_idx == 3, travel_times[("Russian Hill", friends[3]["location"])],
                     If(first_idx == 4, travel_times[("Russian Hill", friends[4]["location"])],
                     If(first_idx == 5, travel_times[("Russian Hill", friends[5]["location"])],
                     If(first_idx == 6, travel_times[("Russian Hill", friends[6]["location"])],
                     If(first_idx == 7, travel_times[("Russian Hill", friends[7]["location"])],
                     If(first_idx == 8, travel_times[("Russian Hill", friends[8]["location"])],
                     0)))))))))
    
    # Constrain that if any meeting is scheduled, then first_idx must indicate the earliest meeting.
    # The earliest meeting must be reachable from Russian Hill at 9:00 (i.e. 540 minutes) considering travel time.
    first_meeting_constraints = And(
        first_idx >= 0, first_idx < n,
        x_vars[first_idx],
        s_first >= 540 + travel_from_RH,
        *[Implies(x_vars[i], s_first <= s_vars[i]) for i in range(n)]
    )
    # Allow the possibility of no meetings scheduled.
    opt.add(Or(total_meetings == 0, first_meeting_constraints))
    
    # Set the objective: maximize the number of meetings scheduled.
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        mod = opt.model()
        itinerary = []
        scheduled_meetings = []
        for i in range(n):
            if is_true(mod.evaluate(x_vars[i])):
                start_val = mod.evaluate(s_vars[i]).as_long()
                end_val = mod.evaluate(e_vars[i]).as_long()
                scheduled_meetings.append((start_val, i, end_val))
        # Sort scheduled meetings in order of their start times.
        scheduled_meetings.sort(key=lambda tup: tup[0])
        for (start_val, i, end_val) in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()