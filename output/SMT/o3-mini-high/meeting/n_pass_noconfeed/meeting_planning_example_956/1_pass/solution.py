from z3 import Optimize, Int, If, And, Or, Implies, Sum, sat
import json

def format_time(t):
    # Given time in minutes from midnight, return string "H:MM" (24-hour format)
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

# Define friends data with availability (in minutes from midnight) and required meeting durations
friends = [
    {"name": "William", "location": "Alamo Square", "avail_start": 15*60+15, "avail_end": 17*60+15, "min_duration": 60},
    {"name": "Joshua", "location": "Richmond District", "avail_start": 7*60, "avail_end": 20*60, "min_duration": 15},
    {"name": "Joseph", "location": "Financial District", "avail_start": 11*60+15, "avail_end": 13*60+30, "min_duration": 15},
    {"name": "David", "location": "Union Square", "avail_start": 16*60+45, "avail_end": 19*60+15, "min_duration": 45},
    {"name": "Brian", "location": "Fisherman's Wharf", "avail_start": 13*60+45, "avail_end": 20*60+45, "min_duration": 105},
    {"name": "Karen", "location": "Marina District", "avail_start": 11*60+30, "avail_end": 18*60+30, "min_duration": 15},
    {"name": "Anthony", "location": "Haight-Ashbury", "avail_start": 7*60+15, "avail_end": 10*60+30, "min_duration": 30},
    {"name": "Matthew", "location": "Mission District", "avail_start": 17*60+15, "avail_end": 19*60+15, "min_duration": 120},
    {"name": "Helen", "location": "Pacific Heights", "avail_start": 8*60, "avail_end": 12*60, "min_duration": 75},
    {"name": "Jeffrey", "location": "Golden Gate Park", "avail_start": 19*60, "avail_end": 21*60+30, "min_duration": 60}
]

# Define travel times (in minutes) between locations.
# Keys are (origin, destination) tuples.
travel_times = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

# Maximum number of meeting slots (at most one per friend)
n_slots = len(friends)

opt = Optimize()

# Create decision variables:
# slot_friend[i] will be -1 if slot is unused, or an index into friends (0..len(friends)-1) if used.
slot_friend = [Int(f"slot_friend_{i}") for i in range(n_slots)]
slot_start = [Int(f"slot_start_{i}") for i in range(n_slots)]
slot_end   = [Int(f"slot_end_{i}") for i in range(n_slots)]

# Add domain constraints and link unused slots to zero times.
for i in range(n_slots):
    # Either unused (-1) or a valid friend index [0, len(friends)-1]
    opt.add(Or(slot_friend[i] == -1, And(slot_friend[i] >= 0, slot_friend[i] < len(friends))))
    # Time bounds: we assume the day is within 0 and 1440 minutes (24 hours)
    opt.add(slot_start[i] >= 0, slot_start[i] <= 1440)
    opt.add(slot_end[i] >= 0, slot_end[i] <= 1440)
    # If not scheduled, times are 0.
    opt.add(Implies(slot_friend[i] == -1, And(slot_start[i] == 0, slot_end[i] == 0)))
    # If scheduled, ensure meeting has positive duration (this will be further constrained by friend availabilities)
    opt.add(Implies(slot_friend[i] != -1, slot_end[i] - slot_start[i] > 0))

# For each slot used, enforce the meeting must occur within the friend's available window and satisfy minimum duration.
for i in range(n_slots):
    for k in range(len(friends)):
        opt.add(Implies(slot_friend[i] == k,
                        And(
                            slot_start[i] >= friends[k]["avail_start"],
                            slot_end[i]   <= friends[k]["avail_end"],
                            slot_end[i] - slot_start[i] >= friends[k]["min_duration"]
                        )))

# Ensure that once an unused slot is encountered, all later slots are unused (contiguity of the scheduled meetings)
for i in range(n_slots - 1):
    opt.add(Implies(slot_friend[i] == -1, slot_friend[i+1] == -1))

# Ensure that each friend is scheduled at most once.
for i in range(n_slots):
    for j in range(i+1, n_slots):
        opt.add(Or(slot_friend[i] == -1, slot_friend[j] == -1, slot_friend[i] != slot_friend[j]))

# Travel constraints:
# For the first meeting, travel from the starting location ("The Castro") at 9:00 (540 minutes)
for k in range(len(friends)):
    # Get travel time from "The Castro" to the friend's location
    if ("The Castro", friends[k]["location"]) in travel_times:
        travel_time_val = travel_times[("The Castro", friends[k]["location"])]
        opt.add(Implies(slot_friend[0] == k, slot_start[0] >= 540 + travel_time_val))

# For subsequent meetings, add travel constraints between consecutive meetings.
for i in range(1, n_slots):
    for k in range(len(friends)):
        for j in range(len(friends)):
            if (friends[k]["location"], friends[j]["location"]) in travel_times:
                travel_time_val = travel_times[(friends[k]["location"], friends[j]["location"])]
                opt.add(Implies(And(slot_friend[i-1] == k, slot_friend[i] == j),
                                slot_start[i] >= slot_end[i-1] + travel_time_val))

# Objective: Maximize number of meetings scheduled.
total_meetings = Sum([If(slot_friend[i] != -1, 1, 0) for i in range(n_slots)])
opt.maximize(total_meetings)

# Check and extract the model
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for i in range(n_slots):
        f_index = model.evaluate(slot_friend[i]).as_long()
        # If this slot is unused, break (since they are contiguous)
        if f_index == -1:
            break
        start_time = model.evaluate(slot_start[i]).as_long()
        end_time = model.evaluate(slot_end[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": friends[f_index]["location"],
            "person": friends[f_index]["name"],
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))