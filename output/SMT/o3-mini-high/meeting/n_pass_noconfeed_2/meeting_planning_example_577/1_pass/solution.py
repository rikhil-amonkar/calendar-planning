import json
from z3 import Optimize, Int, Bool, If, Implies, Or, And, Sum, sat

# Travel times in minutes between locations
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
    ("Pacific Heights", "Alamo Square"): 10
}

# Friend meeting constraints:
# Times are represented as minutes from midnight.
# 9:00 AM = 540, 7:45AM = 465, 10:30AM = 630, 8:30AM = 510, 17:00 = 1020,
# 7:15PM = 1155, 8:00PM = 1200, 8:45PM = 1245, 7:45PM = 1185, 9:45PM = 1305.
friends = [
    {"name": "Stephanie", "location": "Russian Hill", "avail_start": 1200, "avail_end": 1245, "duration": 15},
    {"name": "Kevin", "location": "Fisherman's Wharf", "avail_start": 1155, "avail_end": 1305, "duration": 75},
    {"name": "Robert", "location": "Nob Hill", "avail_start": 465, "avail_end": 630, "duration": 90},
    {"name": "Steven", "location": "Golden Gate Park", "avail_start": 510, "avail_end": 1020, "duration": 75},
    {"name": "Anthony", "location": "Alamo Square", "avail_start": 465, "avail_end": 1185, "duration": 15},
    {"name": "Sandra", "location": "Pacific Heights", "avail_start": 885, "avail_end": 1305, "duration": 45}
]

# You start at Haight-Ashbury at 9:00 AM (540 minutes)
start_location = "Haight-Ashbury"
start_time = 540

def format_time(t):
    # Converts minutes since midnight to "H:MM" 24-hour format without a leading zero on hour.
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()
    
    # For each friend we create decision variables:
    # - a Boolean variable indicating whether to attend their meeting.
    # - an integer variable representing the meeting start time (in minutes from midnight).
    friend_vars = []
    for f in friends:
        var = {}
        var["attend"] = Bool(f"attend_{f['name']}")
        var["start"] = Int(f"start_{f['name']}")
        var["duration"] = f["duration"]
        var["avail_start"] = f["avail_start"]
        var["avail_end"] = f["avail_end"]
        var["name"] = f["name"]
        var["location"] = f["location"]
        friend_vars.append(var)
    
    # Constraint: If you decide to attend a meeting, then the meeting must start within the friend’s availability
    # and be long enough, and you must also have time to travel from your starting point.
    for var in friend_vars:
        # Meeting must not start before the friend is available.
        opt.add(Implies(var["attend"], var["start"] >= var["avail_start"]))
        # Meeting must finish within the friend’s availability window.
        opt.add(Implies(var["attend"], var["start"] + var["duration"] <= var["avail_end"]))
        # You must travel from the starting location to the meeting location.
        travel_from_start = travel_times[(start_location, var["location"])]
        opt.add(Implies(var["attend"], var["start"] >= start_time + travel_from_start))
    
    # For any two meetings that are scheduled, enforce that they do not overlap
    # and that travel time between their locations is accounted for.
    n = len(friend_vars)
    for i in range(n):
        for j in range(i + 1, n):
            vi = friend_vars[i]
            vj = friend_vars[j]
            travel_ij = travel_times[(vi["location"], vj["location"])]
            travel_ji = travel_times[(vj["location"], vi["location"])]
            # If both meetings are attended then either meeting i happens before meeting j or vice versa.
            opt.add(Implies(And(vi["attend"], vj["attend"]),
                            Or(vi["start"] + vi["duration"] + travel_ij <= vj["start"],
                               vj["start"] + vj["duration"] + travel_ji <= vi["start"])))
    
    # Objective: maximize the number of meetings attended.
    total_meetings = Sum([If(var["attend"], 1, 0) for var in friend_vars])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Collect the meetings that are scheduled (attend == True) and compute their start and end times.
        for var in friend_vars:
            if model.evaluate(var["attend"]):
                meeting_start = model.evaluate(var["start"]).as_long()
                meeting_end = meeting_start + var["duration"]
                itinerary.append({
                    "action": "meet",
                    "location": var["location"],
                    "person": var["name"],
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                })
        # Sort the meetings in chronological order based on the meeting start time.
        def time_to_minutes(time_str):
            parts = time_str.split(":")
            return int(parts[0]) * 60 + int(parts[1])
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()