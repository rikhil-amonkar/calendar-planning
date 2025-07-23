import json
from z3 import *

# Travel times between districts (in minutes)
travel_times = {
    "Mission District": {"Mission District": 0, "The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19, "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20},
    "The Castro": {"Mission District": 7, "The Castro": 0, "Nob Hill": 16, "Presidio": 20, "Marina District": 21, "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16},
    "Nob Hill": {"Mission District": 13, "The Castro": 17, "Nob Hill": 0, "Presidio": 17, "Marina District": 11, "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14},
    "Presidio": {"Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Presidio": 0, "Marina District": 11, "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7},
    "Marina District": {"Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10, "Marina District": 0, "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11},
    "Pacific Heights": {"Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11, "Marina District": 6, "Pacific Heights": 0, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12},
    "Golden Gate Park": {"Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11, "Marina District": 16, "Pacific Heights": 16, "Golden Gate Park": 0, "Chinatown": 23, "Richmond District": 7},
    "Chinatown": {"Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19, "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Chinatown": 0, "Richmond District": 20},
    "Richmond District": {"Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7, "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20, "Richmond District": 0}
}

# Friends data: (name, district, start_min, end_min, min_duration)
friends = [
    ("Daniel", "Nob Hill", 0, 120, 15),          # 9:00-11:00
    ("Betty", "Richmond District", 255, 405, 30), # 13:15-15:45
    ("Kevin", "Chinatown", 180, 600, 30),         # 12:00-19:00
    ("Timothy", "Pacific Heights", 180, 540, 90), # 12:00-18:00
    ("Steven", "Marina District", 450, 705, 90),  # 16:30-20:45
    ("Lisa", "The Castro", 615, 735, 120),        # 19:15-21:15
    ("Ashley", "Golden Gate Park", 705, 765, 60), # 20:45-21:45
    ("Elizabeth", "Presidio", 735, 795, 45)       # 21:15-22:15
]

s = Optimize()

# Decision variables
meet_vars = {name: Bool(f'meet_{name}') for name, _, _, _, _ in friends}
start_vars = {name: Int(f'start_{name}') for name, _, _, _, _ in friends}
end_vars = {name: Int(f'end_{name}') for name, _, _, _, _ in friends}

# Time window and duration constraints
for name, loc, win_start, win_end, dur in friends:
    s.add(If(meet_vars[name],
             And(start_vars[name] >= win_start,
                 end_vars[name] == start_vars[name] + dur,
                 end_vars[name] <= win_end),
             True))

# First meeting must account for travel from Mission District
for name, loc, _, _, _ in friends:
    travel_time = travel_times["Mission District"][loc]
    s.add(If(meet_vars[name], start_vars[name] >= travel_time, True))

# All meetings must be in chronological order
ordered_friends = [name for name, _, _, _, _ in friends]
for i in range(len(ordered_friends)):
    for j in range(i+1, len(ordered_friends)):
        name_i = ordered_friends[i]
        name_j = ordered_friends[j]
        s.add(If(And(meet_vars[name_i], meet_vars[name_j]),
                 start_vars[name_j] >= end_vars[name_i],
                 True))

# Travel time constraints between all meeting pairs
for i, (name1, loc1, _, _, dur1) in enumerate(friends):
    for j, (name2, loc2, _, _, dur2) in enumerate(friends):
        if i == j: 
            continue
        travel_time = travel_times[loc1][loc2]
        s.add(If(And(meet_vars[name1], meet_vars[name2]),
                 Or(start_vars[name2] >= end_vars[name1] + travel_time, 
                    start_vars[name1] >= end_vars[name2] + travel_time),
                 True))

# Maximize number of meetings
s.maximize(Sum([If(meet_vars[name], 1, 0) for name, _, _, _, _ in friends]))

if s.check() == sat:
    model = s.model()
    meetings = []
    for name, loc, _, _, dur in friends:
        if model.evaluate(meet_vars[name]):
            start_val = model.evaluate(start_vars[name]).as_long()
            end_val = start_val + dur
            
            # Convert to HH:MM format
            start_hour = 9 + start_val // 60
            start_minute = start_val % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            end_str = f"{end_hour}:{end_minute:02d}"
            
            meetings.append((start_val, name, start_str, end_str))
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x[0])
    itinerary = [{"action": "meet", "person": name, "start_time": st, "end_time": et} 
                 for _, name, st, et in meetings]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')