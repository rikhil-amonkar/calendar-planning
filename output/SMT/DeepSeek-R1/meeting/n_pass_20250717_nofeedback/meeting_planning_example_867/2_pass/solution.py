from z3 import *
import json

# Define travel times between locations
travel_times = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Union Square": 19,
        "Pacific Heights": 12,
        "Bayview": 18,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Richmond District": 10,
        "Sunset District": 15,
        "Golden Gate Park": 7
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Union Square": 15,
        "Pacific Heights": 16,
        "Bayview": 14,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Richmond District": 20,
        "Sunset District": 24,
        "Golden Gate Park": 17
    },
    "Union Square": {
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Bayview": 15,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Union Square": 12,
        "Bayview": 22,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Richmond District": 12,
        "Sunset District": 21,
        "Golden Gate Park": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Union Square": 18,
        "Pacific Heights": 23,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
        "Richmond District": 25,
        "Sunset District": 23,
        "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Union Square": 13,
        "Pacific Heights": 12,
        "Bayview": 26,
        "Marina District": 9,
        "Richmond District": 18,
        "Sunset District": 27,
        "Golden Gate Park": 25
    },
    "Marina District": {
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Union Square": 16,
        "Pacific Heights": 7,
        "Bayview": 27,
        "Fisherman's Wharf": 10,
        "Richmond District": 11,
        "Sunset District": 19,
        "Golden Gate Park": 18
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Union Square": 21,
        "Pacific Heights": 10,
        "Bayview": 27,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Sunset District": 11,
        "Golden Gate Park": 9
    },
    "Sunset District": {
        "Haight-Ashbury": 15,
        "Mission District": 25,
        "Union Square": 30,
        "Pacific Heights": 21,
        "Bayview": 22,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Richmond District": 12,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Union Square": 22,
        "Pacific Heights": 16,
        "Bayview": 23,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Richmond District": 7,
        "Sunset District": 10
    }
}

# Define friends' details: (name, location, window_start, window_end, min_duration)
friends = [
    ("Elizabeth", "Mission District", 630, 1200, 90),      # 10:30 AM to 8:00 PM
    ("David", "Union Square", 915, 1140, 45),              # 3:15 PM to 7:00 PM
    ("Sandra", "Pacific Heights", 420, 1200, 120),         # 7:00 AM to 8:00 PM
    ("Thomas", "Bayview", 1350, 1470, 30),                 # 7:30 PM to 8:30 PM
    ("Robert", "Fisherman's Wharf", 600, 900, 15),         # 10:00 AM to 3:00 PM
    ("Kenneth", "Marina District", 645, 780, 45),          # 10:45 AM to 1:00 PM
    ("Melissa", "Richmond District", 1335, 1440, 15),      # 6:15 PM to 8:00 PM
    ("Kimberly", "Sunset District", 615, 1095, 105),       # 10:15 AM to 6:15 PM
    ("Amanda", "Golden Gate Park", 465, 1125, 15)          # 7:45 AM to 6:45 PM
]

# Initialize Z3 optimizer
opt = Optimize()

# Create variables: meet[i] and start_times[i]
meet = [Bool(f"meet_{i}") for i in range(9)]
start_times = [Int(f"start_{i}") for i in range(9)]

# Constraint: Time windows for each friend if met
for i in range(9):
    name, loc, w_start, w_end, dur = friends[i]
    opt.add(Implies(meet[i], And(start_times[i] >= w_start, start_times[i] + dur <= w_end)))

# Constraint: Travel time from start location (Haight-Ashbury) to each friend
for i in range(9):
    name, loc, w_start, w_end, dur = friends[i]
    travel_from_start = travel_times["Haight-Ashbury"][loc]
    opt.add(Implies(meet[i], start_times[i] >= 540 + travel_from_start))  # 9:00 AM = 540 minutes

# Constraint: For every pair of friends, if both are met, ensure travel time between them is respected
for i in range(9):
    for j in range(i + 1, 9):
        name_i, loc_i, w_start_i, w_end_i, dur_i = friends[i]
        name_j, loc_j, w_start_j, w_end_j, dur_j = friends[j]
        t_ij = travel_times[loc_i][loc_j]
        t_ji = travel_times[loc_j][loc_i]
        # Disjunction: either i then j or j then i
        disj = Or(
            start_times[i] + dur_i + t_ij <= start_times[j],
            start_times[j] + dur_j + t_ji <= start_times[i]
        )
        opt.add(Implies(And(meet[i], meet[j]), disj))

# Objective: Maximize the number of friends met
obj = Sum([If(meet[i], 1, 0) for i in range(9)])
opt.maximize(obj)

# Solve the problem
itinerary = []
if opt.check() == sat:
    m = opt.model()
    # Collect scheduled meetings
    meetings = []
    for i in range(9):
        if m.evaluate(meet[i]):
            start_val = m.evaluate(start_times[i])
            if is_int_value(start_val):
                start_min = start_val.as_long()
                name, loc, w_start, w_end, dur = friends[i]
                end_min = start_min + dur
                # Format time as HH:MM
                start_time_str = f"{start_min // 60:02d}:{start_min % 60:02d}"
                end_time_str = f"{end_min // 60:02d}:{end_min % 60:02d}"
                meetings.append({
                    "person": name,
                    "start_min": start_min,
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
    # Sort meetings by start time
    meetings.sort(key=lambda x: x["start_min"])
    itinerary = [{"action": "meet", "person": m["person"], "start_time": m["start_time"], "end_time": m["end_time"]} for m in meetings]

# Output the solution
print("SOLUTION:")
print(json.dumps({"itinerary": itinerary}))