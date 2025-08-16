from z3 import *
import json

# We measure time in minutes from midnight.
# For example, 9:00AM = 9*60 = 540.

# Travel times (in minutes) between locations – taken directly from the problem.
travel = {
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Mission District"): 15,
    
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Mission District"): 17,
    
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Mission District"): 7,
    
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Mission District"): 13,
    
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Mission District"): 20,
    
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Mission District"): 14,
    
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Mission District"): 25,
    
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
}

# Friend data – each friend has an assigned meeting location, an available time window, and a minimum meeting duration.
friends = {
    "Helen": {
        "location": "Golden Gate Park",
        "window_start": 9*60 + 30,  # 09:30 -> 570
        "window_end": 12*60 + 15,   # 12:15 -> 735
        "duration": 45
    },
    "Steven": {
        "location": "The Castro",
        "window_start": 20*60 + 15, # 20:15 -> 1215
        "window_end": 22*60,        # 22:00 -> 1320
        "duration": 105
    },
    "Deborah": {
        "location": "Bayview",
        "window_start": 8*60 + 30,  # 08:30 -> 510
        "window_end": 12*60,        # 12:00 -> 720
        "duration": 30
    },
    "Matthew": {
        "location": "Marina District",
        "window_start": 9*60 + 15,  # 09:15 -> 555
        "window_end": 14*60 + 15,   # 14:15 -> 855
        "duration": 45
    },
    "Joseph": {
        "location": "Union Square",
        "window_start": 14*60 + 15, # 14:15 -> 855
        "window_end": 18*60 + 45,   # 18:45 -> 1125
        "duration": 120
    },
    "Ronald": {
        "location": "Sunset District",
        "window_start": 16*60,      # 16:00 -> 960
        "window_end": 20*60 + 45,     # 20:45 -> 1245
        "duration": 60
    },
    "Robert": {
        "location": "Alamo Square",
        "window_start": 18*60 + 30, # 18:30 -> 1110
        "window_end": 21*60 + 15,   # 21:15 -> 1275
        "duration": 120
    },
    "Rebecca": {
        "location": "Financial District",
        "window_start": 14*60 + 45, # 14:45 -> 885
        "window_end": 16*60 + 15,   # 16:15 -> 975
        "duration": 30
    },
    "Elizabeth": {
        "location": "Mission District",
        "window_start": 18*60 + 30, # 18:30 -> 1110
        "window_end": 21*60,        # 21:00 -> 1260
        "duration": 120
    }
}

# We use Boolean decision variables x[f] to indicate if friend f is met,
# and an integer variable s[f] for the start time of f’s meeting.
s = {}
x = {}
for f in friends:
    s[f] = Int(f"s_{f}")
    x[f] = Bool(f"x_{f}")

opt = Optimize()

# For each friend, if met then:
# 1. The meeting must start no earlier than the friend’s window start.
# 2. The meeting must finish (start+s.duration) by the friend’s window end.
# 3. The meeting cannot start before we can travel from Pacific Heights (arrival time is 9:00 = 540 plus travel from PH to the friend’s location).
for f, data in friends.items():
    ws = data["window_start"]
    we = data["window_end"]
    dur = data["duration"]
    loc = data["location"]
    opt.add(Implies(x[f], s[f] >= ws))
    opt.add(Implies(x[f], s[f] + dur <= we))
    if ("Pacific Heights", loc) in travel:
        opt.add(Implies(x[f], s[f] >= 540 + travel[("Pacific Heights", loc)]))
    else:
        opt.add(Implies(x[f], s[f] >= 540 + 30))

# To ensure meetings do not overlap we add disjunctive ordering constraints:
# For any two meetings that are scheduled, either one finishes (plus the travel time from its location to the next)
# before the other starts.
friend_list = list(friends.keys())
for i in range(len(friend_list)):
    for j in range(i+1, len(friend_list)):
        f1 = friend_list[i]
        f2 = friend_list[j]
        loc1 = friends[f1]["location"]
        loc2 = friends[f2]["location"]
        dur1 = friends[f1]["duration"]
        dur2 = friends[f2]["duration"]
        t1_to_2 = travel[(loc1, loc2)] if (loc1, loc2) in travel else 30
        t2_to_1 = travel[(loc2, loc1)] if (loc2, loc1) in travel else 30
        ordering = Implies(And(x[f1], x[f2]),
                           Or(s[f1] + dur1 + t1_to_2 <= s[f2],
                              s[f2] + dur2 + t2_to_1 <= s[f1]))
        opt.add(ordering)

# Our objective is to maximize the number of friends met.
total_meetings = Sum([If(x[f], 1, 0) for f in friends])
opt.maximize(total_meetings)

# Solve the model.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    # Extract meetings for friends that are scheduled (x[f] == True).
    for f in friends:
        if is_true(model.evaluate(x[f])):
            start = model.evaluate(s[f]).as_long()
            end = start + friends[f]["duration"]
            scheduled.append((start, f, end))
    # Sort the meetings in chronological order.
    scheduled.sort(key=lambda tup: tup[0])
    
    # Helper: convert minutes to "HH:MM" 24-hour format.
    def minutes_to_hhmm(m):
        hh = m // 60
        mm = m % 60
        return f"{hh:02d}:{mm:02d}"
    
    itinerary = []
    for start, person, end in scheduled:
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": minutes_to_hhmm(start),
            "end_time": minutes_to_hhmm(end)
        })
        
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")