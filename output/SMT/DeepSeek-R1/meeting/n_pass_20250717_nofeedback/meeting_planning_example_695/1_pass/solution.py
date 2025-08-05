from z3 import *
import json

# Travel times dictionary
travel_dict = {
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "The Castro"): 20,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Russian Hill"): 14,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Pacific Heights"): 7
}

# Friend data: name, location, availability start, availability end, minimum duration (all in minutes)
friends = [
    {"name": "Paul", "location": "Nob Hill", "start_avail": 16*60+15, "end_avail": 21*60+15, "min_duration": 60},
    {"name": "Carol", "location": "Union Square", "start_avail": 18*60, "end_avail": 20*60+15, "min_duration": 120},
    {"name": "Patricia", "location": "Chinatown", "start_avail": 20*60, "end_avail": 21*60+30, "min_duration": 75},
    {"name": "Karen", "location": "The Castro", "start_avail": 17*60, "end_avail": 19*60, "min_duration": 45},
    {"name": "Nancy", "location": "Presidio", "start_avail": 11*60+45, "end_avail": 22*60, "min_duration": 30},
    {"name": "Jeffrey", "location": "Pacific Heights", "start_avail": 20*60, "end_avail": 20*60+45, "min_duration": 45},
    {"name": "Matthew", "location": "Russian Hill", "start_avail": 15*60+45, "end_avail": 21*60+45, "min_duration": 75}
]

# Locations for the meetings: index 0 is dummy (Bayview), then the friends in order
locations = ["Bayview"] + [friend["location"] for friend in friends]

# Create Z3 variables and solver
s = Optimize()
num_meetings = len(locations)  # 8: dummy + 7 friends

# meet[i]: whether we meet the i-th meeting (dummy is always met)
meet = [Bool(f"meet_{i}") for i in range(num_meetings)]
start = [Int(f"start_{i}") for i in range(num_meetings)]
end = [Int(f"end_{i}") for i in range(num_meetings)]

# Dummy meeting (index 0) is fixed: at Bayview, 9:00 AM (540 minutes)
s.add(meet[0] == True)
s.add(start[0] == 540)
s.add(end[0] == 540)

# Constraints for friend meetings (indices 1 to 7)
for i in range(1, num_meetings):
    friend = friends[i-1]
    # If we meet this friend, then the meeting must be within their availability and have the minimum duration
    s.add(Implies(meet[i], 
                  And(start[i] >= friend["start_avail"],
                      end[i] <= friend["end_avail"],
                      end[i] == start[i] + friend["min_duration"])))
    # Travel time from dummy (Bayview) to this friend's location
    travel_time = travel_dict[("Bayview", locations[i])]
    s.add(Implies(meet[i], start[i] >= end[0] + travel_time))

# Disjunctive constraints for every pair of friend meetings (i, j) with i < j
for i in range(1, num_meetings):
    for j in range(i+1, num_meetings):
        before_ij = Bool(f"before_{i}_{j}")
        # If both meetings are scheduled, enforce travel time based on order
        s.add(Implies(And(meet[i], meet[j]),
                      If(before_ij,
                         end[i] + travel_dict[(locations[i], locations[j])] <= start[j],
                         end[j] + travel_dict[(locations[j], locations[i])] <= start[i])
                     ))

# Maximize the number of friends met (indices 1 to 7)
s.maximize(Sum([If(meet[i], 1, 0) for i in range(1, num_meetings)]))

# Check and get the model
if s.check() == sat:
    model = s.model()
    scheduled_meetings = []
    for i in range(1, num_meetings):
        if model.evaluate(meet[i]):
            start_val = model.evaluate(start[i])
            end_val = model.evaluate(end[i])
            # Convert to integers
            start_min = start_val.as_long() if is_int_value(start_val) else int(str(start_val))
            end_min = end_val.as_long() if is_int_value(end_val) else int(str(end_val))
            # Convert to HH:MM
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            scheduled_meetings.append({
                "action": "meet",
                "person": friends[i-1]["name"],
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort by start time
    scheduled_meetings.sort(key=lambda x: x["start_time"])
    # Output as JSON
    result = {"itinerary": scheduled_meetings}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')