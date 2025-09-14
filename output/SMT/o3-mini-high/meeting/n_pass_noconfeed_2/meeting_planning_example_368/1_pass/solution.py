#!/usr/bin/env python3
from z3 import *
import json

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Define friend meeting parameters.
    # Times are expressed in minutes after midnight.
    friends = {
        "Joseph": {
            "location": "Russian Hill",
            "avail_start": 8 * 60 + 30,  # 8:30
            "avail_end": 19 * 60 + 15,   # 19:15
            "min_duration": 60
        },
        "Nancy": {
            "location": "Alamo Square",
            "avail_start": 11 * 60,      # 11:00
            "avail_end": 16 * 60,        # 16:00
            "min_duration": 90
        },
        "Jason": {
            "location": "North Beach",
            "avail_start": 16 * 60 + 45, # 16:45
            "avail_end": 21 * 60 + 45,   # 21:45
            "min_duration": 15
        },
        "Jeffrey": {
            "location": "Financial District",
            "avail_start": 10 * 60 + 30, # 10:30
            "avail_end": 15 * 60 + 45,   # 15:45
            "min_duration": 45
        }
    }
    
    # Travel times between locations (in minutes)
    travel_times = {
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Financial District"): 19,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Financial District"): 11,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Russian Hill"): 10,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "North Beach"): 7
    }
    
    # You arrive at Bayview at 9:00AM.
    start_location = "Bayview"
    start_time = 9 * 60  # 9:00 in minutes

    # Create an Optimize instance.
    opt = Optimize()

    # For each friend, create SMT variables for meeting start time (S), end time (E),
    # and the order in which the meeting occurs (order).
    # We also introduce a Boolean 'attend' flag but here we force meeting everyone.
    friend_vars = {}
    for name, info in friends.items():
        S = Int(f"S_{name}")        # Meeting start time
        E = Int(f"E_{name}")        # Meeting end time
        order = Int(f"order_{name}")  # Meeting order index (0, 1, 2, 3)
        attend = Bool(f"attend_{name}")  # Indicates if meeting is scheduled
        
        friend_vars[name] = {
            "S": S,
            "E": E,
            "order": order,
            "attend": attend,
            "info": info
        }
        # We want to meet everyone so set attend to True.
        opt.add(attend == True)
        # Meeting must occur within the friend’s available window.
        opt.add(S >= info["avail_start"])
        opt.add(E <= info["avail_end"])
        # Meeting duration must be at least the minimum required.
        opt.add(E - S >= info["min_duration"])
        # If attended, order must be between 0 and 3.
        opt.add(order >= 0, order < len(friends))
    
    # Enforce that the meetings get a unique order (a permutation of [0, 1, 2, 3]).
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i + 1, len(friend_names)):
            opt.add(friend_vars[friend_names[i]]["order"] != friend_vars[friend_names[j]]["order"])
    
    # For the first meeting in the itinerary (order == 0), you must travel
    # from the start location (Bayview) to the friend's location.
    for name in friend_names:
        loc = friend_vars[name]["info"]["location"]
        travel_from_start = travel_times[(start_location, loc)]
        opt.add(Implies(friend_vars[name]["order"] == 0, friend_vars[name]["S"] >= start_time + travel_from_start))
    
    # Add travel constraints for consecutive meetings.
    # For any two different friends i and j, if j’s order is exactly one more than i’s,
    # then the meeting with friend j cannot start until after friend i’s meeting ends plus the travel time
    # from friend i’s location to friend j’s location.
    for name_i in friend_names:
        for name_j in friend_names:
            if name_i == name_j:
                continue
            loc_i = friend_vars[name_i]["info"]["location"]
            loc_j = friend_vars[name_j]["info"]["location"]
            travel_ij = travel_times[(loc_i, loc_j)]
            opt.add(Implies(friend_vars[name_j]["order"] == friend_vars[name_i]["order"] + 1,
                            friend_vars[name_j]["S"] >= friend_vars[name_i]["E"] + travel_ij))
    
    # To encourage an efficient itinerary (less idle time), we introduce a variable
    # representing the end time of the final meeting.
    E_last = Int("E_last")
    for name in friend_names:
        opt.add(E_last >= friend_vars[name]["E"])
    
    # Our primary objective is to meet as many friends as possible.
    # Since we force attend == True for all, the count is 4.
    meet_count = Sum([If(friend_vars[name]["attend"], 1, 0) for name in friend_names])
    opt.maximize(meet_count)
    # As a secondary objective, minimize the end time of the last meeting.
    opt.minimize(E_last)
    
    if opt.check() == sat:
        model = opt.model()
        # Build the itinerary by sorting the meetings in increasing order.
        itinerary = []
        for name in friend_names:
            order_val = model.evaluate(friend_vars[name]["order"]).as_long()
            S_val = model.evaluate(friend_vars[name]["S"]).as_long()
            E_val = model.evaluate(friend_vars[name]["E"]).as_long()
            loc = friend_vars[name]["info"]["location"]
            itinerary.append((order_val, {
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_str(S_val),
                "end_time": minutes_to_str(E_val)
            }))
        itinerary.sort(key=lambda x: x[0])
        result = {"itinerary": [item[1] for item in itinerary]}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()