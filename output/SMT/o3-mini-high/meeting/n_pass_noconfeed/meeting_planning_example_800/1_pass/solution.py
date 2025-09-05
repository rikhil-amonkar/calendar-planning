#!/usr/bin/env python3
import json
from z3 import *

def time_to_str(m):
    # Convert minutes after midnight to "H:MM" 24-hour format
    h = m // 60
    m_mod = m % 60
    return f"{h}:{m_mod:02d}"

def main():
    # Friend meeting data with availability windows (in minutes after midnight)
    # and required meeting durations (in minutes).
    # Note: 7:00 AM = 420, 9:00 AM = 540, 10:30 AM = 630, etc.
    friends = [
        {"person": "Kimberly", "location": "North Beach", "avail_start": 420, "avail_end": 630, "duration": 15},
        {"person": "Brian",    "location": "Fisherman's Wharf", "avail_start": 570, "avail_end": 930, "duration": 45},
        {"person": "Kenneth",  "location": "Nob Hill", "avail_start": 735, "avail_end": 1035, "duration": 105},
        {"person": "Joseph",   "location": "Embarcadero", "avail_start": 930, "avail_end": 1170, "duration": 75},
        {"person": "Joshua",   "location": "Presidio", "avail_start": 990, "avail_end": 1095, "duration": 105},
        {"person": "Betty",    "location": "Haight-Ashbury", "avail_start": 1140, "avail_end": 1230, "duration": 90},
        {"person": "Steven",   "location": "Mission District", "avail_start": 1170, "avail_end": 1260, "duration": 90},
        {"person": "Melissa",  "location": "The Castro", "avail_start": 1215, "avail_end": 1275, "duration": 30},
        {"person": "Barbara",  "location": "Alamo Square", "avail_start": 1245, "avail_end": 1305, "duration": 15},
    ]
    
    # Travel times (in minutes) between locations.
    travel_times = {
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Haight-Ashbury"): 18,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Haight-Ashbury"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Mission District"): 11,
    }
    
    n = len(friends)
    # Create an Optimize object to maximize the number of meetings
    opt = Optimize()
    
    # Decision variables:
    # x[i] indicates if meeting i is scheduled (True/False)
    # S_vars[i] and E_vars[i] are the start and end times of meeting i (in minutes after midnight)
    # order_vars[i] gives the order position (if scheduled, a value from 1 to n; 0 otherwise)
    x = [Bool(f"x_{i}") for i in range(n)]
    S_vars = [Int(f"S_{i}") for i in range(n)]
    E_vars = [Int(f"E_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    
    # For unscheduled meetings, force S, E, and order to 0.
    for i in range(n):
        opt.add(Implies(Not(x[i]), And(S_vars[i] == 0, E_vars[i] == 0, order_vars[i] == 0)))
        opt.add(Implies(x[i], And(S_vars[i] > 0, E_vars[i] > 0, order_vars[i] > 0)))
        # When scheduled, order must be between 1 and n.
        opt.add(Implies(x[i], And(order_vars[i] >= 1, order_vars[i] <= n)))
        # Domain restrictions on times.
        opt.add(S_vars[i] >= 0, S_vars[i] <= 1440)
        opt.add(E_vars[i] >= 0, E_vars[i] <= 1440)
    
    # Each meeting, if scheduled, must occur within the friend's available window,
    # and last at least the required duration.
    for i, friend in enumerate(friends):
        opt.add(Implies(x[i], S_vars[i] >= friend["avail_start"]))
        opt.add(Implies(x[i], E_vars[i] <= friend["avail_end"]))
        opt.add(Implies(x[i], E_vars[i] - S_vars[i] >= friend["duration"]))
    
    # The day starts at Union Square at 9:00 (540 minutes).
    # For the first meeting in the order, ensure that travel from Union Square is considered.
    for i, friend in enumerate(friends):
        travel_from_us = travel_times.get(("Union Square", friend["location"]), 0)
        opt.add(Implies(And(x[i], order_vars[i] == 1), S_vars[i] >= 540 + travel_from_us))
    
    # For any two scheduled meetings, if meeting i comes before meeting j,
    # then the end time of i plus travel time from i's location to j's location must be <= the start time of j.
    for i in range(n):
        for j in range(n):
            if i != j:
                travel_ij = travel_times[(friends[i]["location"], friends[j]["location"])]
                opt.add(Implies(And(x[i], x[j], order_vars[i] < order_vars[j]),
                                  E_vars[i] + travel_ij <= S_vars[j]))
    
    # Ensure that scheduled meetings get distinct order positions.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(x[i], x[j]), order_vars[i] != order_vars[j]))
    
    # Our objective is to maximize the total number of meetings scheduled.
    opt.maximize(Sum([If(x[i], 1, 0) for i in range(n)]))
    
    # Solve the SMT model.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(x[i])):
                scheduled.append((model.evaluate(order_vars[i]).as_long(), i))
        # Sort scheduled meetings by their order.
        scheduled.sort(key=lambda t: t[0])
        
        itinerary = []
        for order_val, i in scheduled:
            start_time = model.evaluate(S_vars[i]).as_long()
            end_time = model.evaluate(E_vars[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["person"],
                "start_time": time_to_str(start_time),
                "end_time": time_to_str(end_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # If no feasible schedule was found
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()