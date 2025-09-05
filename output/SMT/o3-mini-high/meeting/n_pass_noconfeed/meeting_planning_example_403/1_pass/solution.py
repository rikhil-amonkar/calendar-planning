#!/usr/bin/env python3
from z3 import *
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times in minutes between locations.
    travel = {
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "The Castro"): 19,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "The Castro"): 13,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "The Castro"): 16,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "The Castro"): 21,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "The Castro"): 22,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Chinatown"): 20,
    }
    
    # Friends' meeting information.
    # Times are represented as minutes after midnight.
    # 9:00 AM is 540 minutes after midnight.
    # For each friend, we capture:
    #   - location
    #   - availability window [avail_start, avail_end]
    #   - minimum meeting duration (in minutes)
    #   - travel time from Union Square (our start point)
    friends = {
        "Andrew": {
            "location": "Golden Gate Park",
            "avail_start": 11 * 60 + 45,   # 705
            "avail_end": 14 * 60 + 30,       # 870
            "min_duration": 75,
            "us_travel": travel[("Union Square", "Golden Gate Park")]
        },
        "Sarah": {
            "location": "Pacific Heights",
            "avail_start": 16 * 60 + 15,     # 975
            "avail_end": 18 * 60 + 45,       # 1125
            "min_duration": 15,
            "us_travel": travel[("Union Square", "Pacific Heights")]
        },
        "Nancy": {
            "location": "Presidio",
            "avail_start": 17 * 60 + 30,     # 1050
            "avail_end": 19 * 60 + 15,       # 1155
            "min_duration": 60,
            "us_travel": travel[("Union Square", "Presidio")]
        },
        "Rebecca": {
            "location": "Chinatown",
            "avail_start": 9 * 60 + 45,      # 585
            "avail_end": 21 * 60 + 30,       # 1290
            "min_duration": 90,
            "us_travel": travel[("Union Square", "Chinatown")]
        },
        "Robert": {
            "location": "The Castro",
            "avail_start": 8 * 60 + 30,      # 510
            "avail_end": 14 * 60 + 15,       # 855
            "min_duration": 30,
            "us_travel": travel[("Union Square", "The Castro")]
        }
    }
    
    # Create an optimizer instance.
    opt = Optimize()
    
    # Create decision variables for each friend:
    # meet_vars indicates if we choose to schedule a meeting with that friend.
    # start_vars indicates the meeting start time (in minutes after midnight) if scheduled.
    meet_vars = {}
    start_vars = {}
    for name in friends:
        meet_vars[name] = Bool("meet_" + name)
        start_vars[name] = Int("start_" + name)
    
    # Add constraints for each friend if a meeting is scheduled.
    # The meeting must begin no earlier than both the friend's availability and
    # the time needed to travel from Union Square (arrival at 9:00 plus travel time).
    for name, info in friends.items():
        lower_bound = max(info["avail_start"], 540 + info["us_travel"])
        opt.add(Implies(meet_vars[name], start_vars[name] >= lower_bound))
        opt.add(Implies(meet_vars[name], start_vars[name] + info["min_duration"] <= info["avail_end"]))
    
    # For any two meetings that are scheduled, add disjunctive non-overlap constraints,
    # taking into account the travel time between their locations.
    friend_names = list(friends.keys())
    n = len(friend_names)
    for i in range(n):
        for j in range(i+1, n):
            name_i = friend_names[i]
            name_j = friend_names[j]
            loc_i = friends[name_i]["location"]
            loc_j = friends[name_j]["location"]
            duration_i = friends[name_i]["min_duration"]
            duration_j = friends[name_j]["min_duration"]
            travel_ij = travel[(loc_i, loc_j)]
            travel_ji = travel[(loc_j, loc_i)]
            # Either meeting i finishes (plus travel time) before meeting j starts or vice-versa.
            no_overlap = Or(
                start_vars[name_i] + duration_i + travel_ij <= start_vars[name_j],
                start_vars[name_j] + duration_j + travel_ji <= start_vars[name_i]
            )
            opt.add(Implies(And(meet_vars[name_i], meet_vars[name_j]), no_overlap))
    
    # Objective: maximize the number of friends met.
    opt.maximize(Sum([If(meet_vars[name], 1, 0) for name in friends]))
    
    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        # Extract meeting details for friends that are scheduled.
        for name, info in friends.items():
            if model.evaluate(meet_vars[name]):
                start_time = model.evaluate(start_vars[name]).as_long()
                end_time = start_time + info["min_duration"]
                scheduled.append({
                    "person": name,
                    "location": info["location"],
                    "start": start_time,
                    "end": end_time
                })
        # Sort the scheduled meetings by their start time.
        scheduled.sort(key=lambda x: x["start"])
        itinerary = []
        for meet in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time(meet["start"]),
                "end_time": minutes_to_time(meet["end"])
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
    
if __name__ == "__main__":
    main()