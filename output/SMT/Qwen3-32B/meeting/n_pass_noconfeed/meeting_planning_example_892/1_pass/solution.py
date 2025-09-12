import json
from z3 import *

friends = [
    {"name": "Laura", "location": 9, "available_start": 465, "available_end": 795, "min_duration": 105},
    {"name": "Charles", "location": 1, "available_start": 690, "available_end": 870, "min_duration": 45},
    {"name": "Robert", "location": 2, "available_start": 1005, "available_end": 1260, "min_duration": 30},
    {"name": "Karen", "location": 3, "available_start": 1155, "available_end": 1290, "min_duration": 60},
    {"name": "Rebecca", "location": 4, "available_start": 975, "available_end": 1230, "min_duration": 90},
    {"name": "Margaret", "location": 5, "available_start": 855, "available_end": 1185, "min_duration": 120},
    {"name": "Patricia", "location": 6, "available_start": 870, "available_end": 1230, "min_duration": 45},
    {"name": "Mark", "location": 7, "available_start": 840, "available_end": 1110, "min_duration": 105},
    {"name": "Melissa", "location": 8, "available_start": 780, "available_end": 1185, "min_duration": 30},
]

travel_time = [
    [0, 27, 19, 11, 12, 15, 16, 11, 8, 14],
    [27, 0, 23, 25, 20, 19, 19, 22, 23, 19],
    [21, 22, 0, 12, 27, 30, 15, 28, 24, 30],
    [9, 27, 11, 0, 17, 20, 10, 17, 13, 19],
    [11, 19, 24, 14, 0, 6, 13, 8, 5, 9],
    [12, 20, 29, 20, 9, 0, 19, 3, 7, 5],
    [17, 18, 15, 10, 15, 19, 0, 19, 17, 20],
    [9, 25, 27, 18, 7, 6, 18, 0, 4, 6],
    [7, 23, 23, 14, 5, 9, 17, 5, 0, 8],
    [12, 21, 30, 21, 10, 7, 21, 5, 8, 0],
]

locations_names = [
    "Marina District",
    "Bayview",
    "Sunset District",
    "Richmond District",
    "Nob Hill",
    "Chinatown",
    "Haight-Ashbury",
    "North Beach",
    "Russian Hill",
    "Embarcadero"
]

N = 9
s = Optimize()

friend_idx = [Int(f"friend_{i}") for i in range(N)]
start_time = [Int(f"start_{i}") for i in range(N)]
end_time = [Int(f"end_{i}") for i in range(N)]

# Constraints for friend indices
for i in range(N):
    s.add(And(friend_idx[i] >= 0, friend_idx[i] <= 9))

# Each friend at most once
for j in range(9):
    sum_vars = [If(friend_idx[i] == j, 1, 0) for i in range(N)]
    s.add(Sum(sum_vars) <= 1)

# Per event constraints
for i in range(N):
    for j in range(9):
        loc_j = friends[j]['location']
        avail_start_j = friends[j]['available_start']
        avail_end_j = friends[j]['available_end']
        min_duration_j = friends[j]['min_duration']
        cond = (friend_idx[i] == j)
        s.add(Implies(cond, start_time[i] >= avail_start_j))
        s.add(Implies(cond, end_time[i] == start_time[i] + min_duration_j))
        s.add(Implies(cond, end_time[i] <= avail_end_j))
        if i == 0:
            travel = travel_time[0][loc_j]
            s.add(Implies(cond, start_time[i] >= 540 + travel))
        if i > 0:
            for k in range(9):
                prev_loc = friends[k]['location']
                travel = travel_time[prev_loc][loc_j]
                prev_cond = (friend_idx[i-1] == k)
                s.add(Implies(And(prev_cond, cond), start_time[i] >= end_time[i-1] + travel))

# Maximize the number of friends
selected_count = Sum([If(friend_idx[i] != 9, 1, 0) for i in range(N)])
s.maximize(selected_count)

if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(N):
        fid = model.evaluate(friend_idx[i])
        if fid != 9:
            j = fid.as_long()
            st = model.evaluate(start_time[i]).as_long()
            et = model.evaluate(end_time[i]).as_long()
            loc_idx = friends[j]['location']
            loc_name = locations_names[loc_idx]
            name = friends[j]['name']
            def to_time_str(m):
                h = m // 60
                mm = m % 60
                return f"{h}:{mm:02d}"
            start_str = to_time_str(st)
            end_str = to_time_str(et)
            itinerary.append({
                "action": "meet",
                "location": loc_name,
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")