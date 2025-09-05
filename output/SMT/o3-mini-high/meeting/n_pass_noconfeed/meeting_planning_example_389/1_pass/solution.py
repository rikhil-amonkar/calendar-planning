#!/usr/bin/env python3
from z3 import *
import json

def min_to_time(minutes):
    # Convert minutes since midnight into H:MM (24-hour format)
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Starting point information
    start_time = 540  # 9:00 AM in minutes since midnight

    # Friend meeting parameters.
    # Times are represented as minutes since midnight.
    friends = {
        "Sarah": {
            "location": "Fisherman's Wharf",
            "avail_start": 885,    # 14:45 (2:45 PM)
            "avail_end": 1050,     # 17:30 (5:30 PM)
            "min_duration": 105,
            "travel_from_start": 23
        },
        "Mary": {
            "location": "Richmond District",
            "avail_start": 780,    # 13:00 (1:00 PM)
            "avail_end": 1155,     # 19:15 (7:15 PM)
            "min_duration": 75,
            "travel_from_start": 10
        },
        "Helen": {
            "location": "Mission District",
            "avail_start": 1305,   # 21:45 (9:45 PM)
            "avail_end": 1350,     # 22:30 (10:30 PM)
            "min_duration": 30,
            "travel_from_start": 11
        },
        "Thomas": {
            "location": "Bayview",
            "avail_start": 915,    # 15:15 (3:15 PM)
            "avail_end": 1125,     # 18:45 (6:45 PM)
            "min_duration": 120,
            "travel_from_start": 18
        }
    }

    # Travel times in minutes between locations.
    # Key is a tuple: (origin_location, destination_location).
    travel_times = {
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Bayview"): 26,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Bayview"): 15,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Mission District"): 13,
    }

    # Create an Optimize() object to maximize the number of meetings (friends attended)
    opt = Optimize()

    # Decision variables: For each friend, create:
    # - meeting_start: when the meeting starts (if attended)
    # - meeting_end: when the meeting ends (if attended)
    # - order: an integer indicating the order in which the meeting occurs (0 means not scheduled)
    meeting_start = {}
    meeting_end = {}
    order_vars = {}

    for friend, info in friends.items():
        meeting_start[friend] = Int(f"{friend}_start")
        meeting_end[friend] = Int(f"{friend}_end")
        order_vars[friend] = Int(f"{friend}_order")
        # Order domain: 0 means not scheduled; positive values 1...4 indicate the meeting’s position.
        opt.add(order_vars[friend] >= 0, order_vars[friend] <= 4)
        
        # If the friend is scheduled (order > 0) then:
        #   - The meeting must happen within the friend's available time window.
        #   - The meeting must last at least the required minimum duration.
        opt.add(Implies(order_vars[friend] > 0,
                        And(meeting_start[friend] >= info["avail_start"],
                            meeting_end[friend] <= info["avail_end"],
                            meeting_end[friend] - meeting_start[friend] >= info["min_duration"])))
        # If this meeting is the first meeting, account for travel from Haight-Ashbury.
        opt.add(Implies(order_vars[friend] == 1,
                        meeting_start[friend] >= start_time + info["travel_from_start"]))
    
    # For any two distinct scheduled meetings, enforce that their order numbers are different.
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        for j in range(i + 1, len(friend_list)):
            f1 = friend_list[i]
            f2 = friend_list[j]
            opt.add(Implies(And(order_vars[f1] > 0, order_vars[f2] > 0),
                            order_vars[f1] != order_vars[f2]))
    
    # For any two friends f and g that are scheduled consecutively, add the travel time constraint.
    # If friend f has order k and friend g has order k+1 (for some k) then
    # the start time of g must be at least the end time of f plus the travel time from f's location to g's.
    for f in friend_list:
        for g in friend_list:
            if f != g:
                # Get travel time from friend f's location to friend g's location.
                if (friends[f]["location"], friends[g]["location"]) in travel_times:
                    t_time = travel_times[(friends[f]["location"], friends[g]["location"])]
                    opt.add(Implies(And(order_vars[f] > 0, order_vars[g] > 0, order_vars[g] == order_vars[f] + 1),
                                    meeting_start[g] >= meeting_end[f] + t_time))
    
    # Enforce contiguity:
    # If any meeting is scheduled in position k (for k = 2, 3, 4), then there must be at least one meeting scheduled in position k-1.
    for k in [2, 3, 4]:
        opt.add(Implies(Or([order_vars[friend] == k for friend in friend_list]),
                        Or([order_vars[friend] == k - 1 for friend in friend_list])))

    # Objective: maximize the total number of meetings attended.
    attendance = [If(order_vars[friend] > 0, 1, 0) for friend in friend_list]
    opt.maximize(Sum(attendance))
    
    # Check the model and extract the solution.
    if opt.check() == sat:
        model = opt.model()
        # Collect all scheduled meetings (order > 0) and sort them by their order.
        scheduled = []
        for friend in friend_list:
            if model.evaluate(order_vars[friend]) is not None and model.evaluate(order_vars[friend]).as_long() > 0:
                scheduled.append((model.evaluate(order_vars[friend]).as_long(), friend))
        scheduled.sort(key=lambda x: x[0])
        
        itinerary = []
        for _, friend in scheduled:
            start_val = model.evaluate(meeting_start[friend]).as_long()
            end_val = model.evaluate(meeting_end[friend]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[friend]["location"],
                "person": friend,
                "start_time": min_to_time(start_val),
                "end_time": min_to_time(end_val)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # No valid schedule was found.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()