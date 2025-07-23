from z3 import *
import json

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

all_locations = ["Bayview", "Nob Hill", "Union Square", "Chinatown", "The Castro", "Presidio", "Pacific Heights", "Russian Hill"]
travel_time_fixed = travel_dict.copy()

# Add zero-minute travel times for all self-locations
for loc in all_locations:
    travel_time_fixed[(loc, loc)] = 0

# Fill missing entries with reverse direction times or default 30 minutes
for from_loc in all_locations:
    for to_loc in all_locations:
        if (from_loc, to_loc) not in travel_time_fixed:
            reverse_key = (to_loc, from_loc)
            travel_time_fixed[(from_loc, to_loc)] = travel_time_fixed.get(reverse_key, 30)

friends = [
    {"name": "Paul", "location": "Nob Hill", "start_avail": 16*60+15, "end_avail": 21*60+15, "min_duration": 60},
    {"name": "Carol", "location": "Union Square", "start_avail": 18*60, "end_avail": 20*60+15, "min_duration": 120},
    {"name": "Patricia", "location": "Chinatown", "start_avail": 20*60, "end_avail": 21*60+30, "min_duration": 75},
    {"name": "Karen", "location": "The Castro", "start_avail": 17*60, "end_avail": 19*60, "min_duration": 45},
    {"name": "Nancy", "location": "Presidio", "start_avail": 11*60+45, "end_avail": 22*60, "min_duration": 30},
    {"name": "Jeffrey", "location": "Pacific Heights", "start_avail": 20*60, "end_avail": 20*60+45, "min_duration": 45},
    {"name": "Matthew", "location": "Russian Hill", "start_avail": 15*60+45, "end_avail": 21*60+45, "min_duration": 75}
]

s = Solver()

num_friends = len(friends)
num_nodes = num_friends + 1

meet = [Bool(f"meet_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_nodes)]
end = [Int(f"end_{i}") for i in range(num_nodes)]

next_mat = [[Bool(f"next_{i}_{j}") for j in range(num_friends)] for i in range(num_nodes)]
pos = [Int(f"pos_{i}") for i in range(num_nodes)]

s.add(start[0] == 540)
s.add(end[0] == 540)

for j in range(1, num_nodes):
    friend = friends[j-1]
    s.add(Implies(meet[j-1], start[j] >= friend["start_avail"]))
    s.add(Implies(meet[j-1], end[j] == start[j] + friend["min_duration"]))
    s.add(Implies(meet[j-1], end[j] <= friend["end_avail"]))

s.add(Sum([If(meet[i], 1, 0) for i in range(num_friends)]) >= 0)

s.add(Sum([next_mat[0][j] for j in range(num_friends)]) == If(Sum([If(meet[i], 1, 0) for i in range(num_friends)]) > 0, 1, 0))

for i in range(1, num_nodes):
    s.add(Sum([next_mat[i][j] for j in range(num_friends)]) == If(meet[i-1], 1, 0))

for j in range(num_friends):
    s.add(Sum([next_mat[i][j] for i in range(num_nodes)]) == meet[j])

s.add(pos[0] == 0)

for i in range(num_nodes):
    for j in range(num_friends):
        s.add(Implies(next_mat[i][j], pos[j+1] == pos[i] + 1))

for i in range(num_nodes):
    for j in range(num_friends):
        if i == 0:
            from_loc = "Bayview"
        else:
            from_loc = friends[i-1]["location"]
        to_loc = friends[j]["location"]
        travel_time = travel_time_fixed[(from_loc, to_loc)]
        s.add(Implies(next_mat[i][j], end[i] + travel_time <= start[j+1]))

for i in range(num_nodes):
    for j in range(i+1, num_nodes):
        if i == 0:
            cond_i = True
        else:
            cond_i = meet[i-1]
        if j == 0:
            cond_j = True
        else:
            cond_j = meet[j-1]
        s.add(Implies(And(cond_i, cond_j), pos[i] != pos[j]))

num_met = Sum([If(meet[i], 1, 0) for i in range(num_friends)])
s.maximize(num_met)

if s.check() == sat:
    m = s.model()
    meetings = []
    for j in range(1, num_nodes):
        if is_true(m.evaluate(meet[j-1])):
            pos_val = m.evaluate(pos[j]).as_long()
            start_val = m.evaluate(start[j]).as_long()
            end_val = m.evaluate(end[j]).as_long()
            friend = friends[j-1]
            meetings.append((pos_val, friend["name"], start_val, end_val))
    meetings.sort(key=lambda x: x[0])
    itinerary = []
    for pos_val, name, start_val, end_val in meetings:
        start_str = f"{start_val//60:02d}:{start_val%60:02d}"
        end_str = f"{end_val//60:02d}:{end_val%60:02d}"
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": start_str,
            "end_time": end_str
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')