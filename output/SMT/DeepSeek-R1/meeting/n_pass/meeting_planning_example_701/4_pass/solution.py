import json
from z3 import *

# Travel times between districts (in minutes)
travel_times = {
    "Mission District": {"The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19, "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20},
    "The Castro": {"Mission District": 7, "Nob Hill": 16, "Presidio": 20, "Marina District": 21, "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16},
    "Nob Hill": {"Mission District": 13, "The Castro": 17, "Presidio": 17, "Marina District": 11, "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14},
    "Presidio": {"Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 11, "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7},
    "Marina District": {"Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10, "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11},
    "Pacific Heights": {"Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11, "Marina District": 6, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12},
    "Golden Gate Park": {"Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11, "Marina District": 16, "Pacific Heights": 16, "Chinatown": 23, "Richmond District": 7},
    "Chinatown": {"Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19, "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Richmond District": 20},
    "Richmond District": {"Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7, "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20}
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

# All meetings must be in chronological order
for i, (name_i, loc_i, _, _, _) in enumerate(friends):
    for name_j, loc_j, _, _, _ in friends[i+1:]:
        s.add(If(And(meet_vars[name_i], meet_vars[name_j]),
                 start_vars[name_j] >= end_vars[name_i],
                 True))

# Travel time constraints from Mission District (start location)
for name, loc, _, _, _ in friends:
    travel = travel_times["Mission District"][loc]
    s.add(If(meet_vars[name], start_vars[name] >= travel, True))

# Travel time constraints between meetings
for name1, loc1, _, _, _ in friends:
    for name2, loc2, _, _, _ in friends:
        if name1 == name2:
            continue
        travel = travel_times[loc1][loc2]
        s.add(If(And(meet_vars[name1], meet_vars[name2]),
                 Or(start_vars[name2] >= end_vars[name1] + travel, 
                    start_vars[name1] >= end_vars[name2] + travel),
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
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            
            meetings.append((start_val, name, start_str, end_str))
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x[0])
    itinerary = [{"action": "meet", "person": name, "start_time": st, "end_time": et} 
                 for _, name, st, et in meetings]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')