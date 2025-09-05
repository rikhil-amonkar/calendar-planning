#!/usr/bin/env python3
import json
from z3 import *

def minutes_to_time(m):
    # Convert minutes since midnight to "H:MM" format (24-hour, no leading zero for hour)
    h = m // 60
    m_rem = m % 60
    return f"{h}:{m_rem:02d}"

def main():
    # Define travel times (in minutes) as given in the problem
    travel_times = {
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Pacific Heights"): 12,

        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Pacific Heights"): 7,

        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Pacific Heights"): 12,

        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Pacific Heights"): 8,

        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Pacific Heights"): 16,

        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Pacific Heights"): 10,

        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
    }

    # Meeting candidate data
    # Times are in minutes since midnight.
    # Arrival at Haight-Ashbury at 9:00AM -> 540 minutes.
    candidates = [
        {
            "name": "Robert",
            "location": "Nob Hill",
            "avail_start": 7 * 60 + 45,  # 465
            "avail_end": 10 * 60 + 30,   # 630
            "duration": 90
        },
        {
            "name": "Stephanie",
            "location": "Russian Hill",
            "avail_start": 20 * 60 + 0,  # 1200
            "avail_end": 20 * 60 + 45,   # 1245
            "duration": 15
        },
        {
            "name": "Kevin",
            "location": "Fisherman's Wharf",
            "avail_start": 19 * 60 + 15,  # 1155
            "avail_end": 21 * 60 + 45,    # 1305
            "duration": 75
        },
        {
            "name": "Steven",
            "location": "Golden Gate Park",
            "avail_start": 8 * 60 + 30,  # 510
            "avail_end": 17 * 60 + 0,    # 1020
            "duration": 75
        },
        {
            "name": "Anthony",
            "location": "Alamo Square",
            "avail_start": 7 * 60 + 45,   # 465
            "avail_end": 19 * 60 + 45,    # 1185
            "duration": 15
        },
        {
            "name": "Sandra",
            "location": "Pacific Heights",
            "avail_start": 14 * 60 + 45,  # 885
            "avail_end": 21 * 60 + 45,    # 1305
            "duration": 45
        },
    ]

    arrival_time = 9 * 60  # 540 minutes (9:00 AM)
    start_location = "Haight-Ashbury"

    # Precompute effective lower bound for each meeting if going directly from arrival.
    # effective_lb = max(avail_start, arrival_time + travel_time(start_location, candidate_location))
    for cand in candidates:
        direct_travel = travel_times[(start_location, cand["location"])]
        cand["lb"] = max(cand["avail_start"], arrival_time + direct_travel)

    solver = Optimize()
    
    n = len(candidates)
    meets = []
    starts = []
    
    # Create Z3 variables for each candidate meeting
    for i in range(n):
        meets.append(Bool(f"meet_{i}"))
        starts.append(Int(f"start_{i}"))
    
    # Add individual meeting constraints: if meeting is scheduled, then
    # its start time must be >= effective lower bound and finish before avail_end.
    for i, cand in enumerate(candidates):
        dur = cand["duration"]
        lb = cand["lb"]
        avail_end = cand["avail_end"]
        # If meeting is chosen, then:
        solver.add(Implies(meets[i], starts[i] >= lb))
        solver.add(Implies(meets[i], starts[i] + dur <= avail_end))
        # Optional: if meeting is not chosen, we do not constrain its start time.
    
    # Add pairwise non-overlap constraints with travel times.
    # For every two meetings that are both scheduled, enforce that either i comes before j (with travel time) or vice versa.
    for i in range(n):
        for j in range(i+1, n):
            loc_i = candidates[i]["location"]
            loc_j = candidates[j]["location"]
            dur_i = candidates[i]["duration"]
            dur_j = candidates[j]["duration"]
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            constraint = Implies(And(meets[i], meets[j]),
                                 Or(starts[i] + dur_i + travel_ij <= starts[j],
                                    starts[j] + dur_j + travel_ji <= starts[i]))
            solver.add(constraint)
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(meets[i], 1, 0) for i in range(n)])
    solver.maximize(total_meetings)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(meets[i])):
                start_time = model.evaluate(starts[i]).as_long()
                end_time = start_time + candidates[i]["duration"]
                scheduled.append({
                    "person": candidates[i]["name"],
                    "location": candidates[i]["location"],
                    "start": start_time,
                    "end": end_time
                })
        # Sort scheduled meetings by start time
        scheduled.sort(key=lambda x: x["start"])
        
        # Build itinerary output in required JSON format
        itinerary = []
        for meet in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time(meet["start"]),
                "end_time": minutes_to_time(meet["end"])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()