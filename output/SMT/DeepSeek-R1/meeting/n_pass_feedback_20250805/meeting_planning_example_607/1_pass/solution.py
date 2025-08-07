from z3 import *
import json

# Define travel times between districts
travel_time = {
    "Sunset District": {
        "Russian Hill": 24,
        "The Castro": 17,
        "Richmond District": 12,
        "Marina District": 21,
        "North Beach": 29,
        "Union Square": 30,
        "Golden Gate Park": 11
    },
    "Russian Hill": {
        "Sunset District": 23,
        "The Castro": 21,
        "Richmond District": 14,
        "Marina District": 7,
        "North Beach": 5,
        "Union Square": 11,
        "Golden Gate Park": 21
    },
    "The Castro": {
        "Sunset District": 17,
        "Russian Hill": 18,
        "Richmond District": 16,
        "Marina District": 21,
        "North Beach": 20,
        "Union Square": 19,
        "Golden Gate Park": 11
    },
    "Richmond District": {
        "Sunset District": 11,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "North Beach": 17,
        "Union Square": 21,
        "Golden Gate Park": 9
    },
    "Marina District": {
        "Sunset District": 19,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "North Beach": 11,
        "Union Square": 16,
        "Golden Gate Park": 18
    },
    "North Beach": {
        "Sunset District": 27,
        "Russian Hill": 4,
        "The Castro": 22,
        "Richmond District": 18,
        "Marina District": 9,
        "Union Square": 7,
        "Golden Gate Park": 22
    },
    "Union Square": {
        "Sunset District": 26,
        "Russian Hill": 13,
        "The Castro": 19,
        "Richmond District": 20,
        "Marina District": 18,
        "North Beach": 10,
        "Golden Gate Park": 22
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Russian Hill": 19,
        "The Castro": 13,
        "Richmond District": 7,
        "Marina District": 16,
        "North Beach": 24,
        "Union Square": 22
    }
}

# Friend data: (name, district, start_available (minutes from 9:00 AM), end_available, min_duration)
friends = [
    ("Karen", "Russian Hill", 705, 765, 60),      # 8:45 PM to 9:45 PM
    ("Jessica", "The Castro", 405, 630, 60),      # 3:45 PM to 7:30 PM
    ("Matthew", "Richmond District", 0, 375, 15), # 7:30 AM to 3:15 PM (effective start 9:00 AM)
    ("Michelle", "Marina District", 90, 585, 75), # 10:30 AM to 6:45 PM
    ("Carol", "North Beach", 180, 480, 90),       # 12:00 PM to 5:00 PM
    ("Stephanie", "Union Square", 105, 315, 30),  # 10:45 AM to 2:15 PM
    ("Linda", "Golden Gate Park", 105, 780, 90)   # 10:45 AM to 10:00 PM
]

# Create Z3 solver
opt = Optimize()

# Variables for each friend: whether we meet, start time, end time, and position in sequence
meet = [Bool(f"meet_{i}") for i in range(7)]
start = [Real(f"start_{i}") for i in range(7)]
end = [Real(f"end_{i}") for i in range(7)]
pos = [Int(f"pos_{i}") for i in range(7)]

# k: total number of meetings
k = Int('k')
opt.add(k == Sum([If(meet[i], 1, 0) for i in range(7)]))

# Constraints for each friend
for i in range(7):
    name, district, s_avail, e_avail, dur = friends[i]
    # If we meet the friend, enforce time constraints
    opt.add(Implies(meet[i], And(
        start[i] >= s_avail,
        end[i] <= e_avail,
        end[i] == start[i] + dur
    )))
    # Position must be between 0 and 6 if met
    opt.add(Implies(meet[i], And(pos[i] >= 0, pos[i] < 7)))
    opt.add(Implies(Not(meet[i]), pos[i] == -1)  # Unused positions set to -1

# Distinct positions for met friends
for i in range(7):
    for j in range(i+1, 7):
        opt.add(Implies(And(meet[i], meet[j]), pos[i] != pos[j]))

# min_val and max_val for positions of met friends
min_val = Int('min_val')
max_val = Int('max_val')

# Initialize min_val and max_val
min_val_temp = 1000
max_val_temp = -1
for i in range(7):
    min_val_temp = If(And(meet[i], pos[i] < min_val_temp), pos[i], min_val_temp)
    max_val_temp = If(And(meet[i], pos[i] > max_val_temp), pos[i], max_val_temp)

# If any meeting, min_val_temp is the min, else 1000; similarly for max_val_temp
any_meet = Or([meet[i] for i in range(7)])
min_val = If(any_meet, min_val_temp, 1000)
max_val = If(any_meet, max_val_temp, -1)

# Positions must be contiguous starting from 0
opt.add(If(k > 0, And(min_val == 0, max_val == k-1), True))

# First meeting constraint: start time >= travel time from Sunset
for i in range(7):
    name, district, s_avail, e_avail, dur = friends[i]
    opt.add(Implies(And(meet[i], pos[i] == 0), 
                start[i] >= travel_time["Sunset District"][district]))

# Consecutive meetings constraint
for i in range(7):
    for j in range(7):
        if i == j:
            continue
        name_i, district_i, _, _, _ = friends[i]
        name_j, district_j, _, _, _ = friends[j]
        # If both met and j is immediately after i
        opt.add(Implies(And(meet[i], meet[j], pos[j] == pos[i] + 1),
                start[j] >= end[i] + travel_time[district_i][district_j]))

# Special constraint: if Karen (index0) is met, Linda (index6) must be met and immediately precede Karen
opt.add(Implies(meet[0], meet[6]))
for p in range(1, 7):
    # If Karen is at position p, Linda must be at position p-1
    opt.add(Implies(And(meet[0], meet[6], pos[0] == p), pos[6] == p-1))

# Maximize the number of friends met
opt.maximize(k)

# Check and get the solution
if opt.check() == sat:
    m = opt.model()
    # Collect meeting details
    itinerary = []
    for i in range(7):
        if is_true(m.eval(meet[i])):
            name = friends[i][0]
            s_val = m.eval(start[i])
            e_val = m.eval(end[i])
            # Convert minutes to time string
            start_min = int(s_val.as_long())
            end_min = int(e_val.as_long())
            start_hour = 9 + start_min // 60
            start_minute = start_min % 60
            end_hour = 9 + end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')