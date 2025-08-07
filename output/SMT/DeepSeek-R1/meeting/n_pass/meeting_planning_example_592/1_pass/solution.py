from z3 import *
import json

# Define travel times between locations
travel_time = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17
    }
}

# Define friends' details
friends = [
    ("James", "Pacific Heights", 20*60, 22*60, 120),  # 8:00PM to 10:00PM
    ("Robert", "Chinatown", 12*60+15, 16*60+45, 90),  # 12:15PM to 4:45PM
    ("Jeffrey", "Union Square", 9*60+30, 15*60+30, 120),  # 9:30AM to 3:30PM
    ("Carol", "Mission District", 18*60+15, 21*60+15, 15),  # 6:15PM to 9:15PM
    ("Mark", "Golden Gate Park", 11*60+30, 17*60+45, 15),  # 11:30AM to 5:45PM
    ("Sandra", "Nob Hill", 8*60, 15*60+30, 15)  # 8:00AM to 3:30PM
]

# Initialize Z3 solver
opt = Optimize()

# Create meet, start, and end variables for each friend
meet = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]
s = [Int(f"s_{name}") for name, _, _, _, _ in friends]
e = [Int(f"e_{name}") for name, _, _, _, _ in friends]

# Create before matrix for 7 nodes (virtual start + 6 friends)
before = [[None]*7 for _ in range(7)]
for i in range(7):
    for j in range(7):
        if i != j:
            before[i][j] = Bool(f"before_{i}_{j}")

# Locations for all nodes (0: virtual start, 1-6: friends)
locs = ["North Beach"] + [loc for _, loc, _, _, _ in friends]

# Constraints for each friend
for idx, (_, _, start_avail, end_avail, min_time) in enumerate(friends):
    opt.add(Implies(meet[idx], s[idx] >= start_avail))
    opt.add(Implies(meet[idx], e[idx] == s[idx] + min_time))
    opt.add(Implies(meet[idx], e[idx] <= end_avail))

# Virtual start must precede any meeting
for idx in range(6):
    opt.add(Implies(meet[idx], before[0][idx+1]))

# Constraints for all distinct pairs of nodes
for i in range(7):
    for j in range(7):
        if i == j:
            continue
        meet_i = True if i == 0 else meet[i-1]
        meet_j = True if j == 0 else meet[j-1]
        opt.add(Implies(And(meet_i, meet_j), Or(before[i][j], before[j][i])))
        opt.add(Implies(And(meet_i, meet_j), Not(And(before[i][j], before[j][i]))))
        # Get start and end times for nodes
        s_i = 540 if i == 0 else s[i-1]
        e_i = 540 if i == 0 else e[i-1]
        s_j = 540 if j == 0 else s[j-1]
        e_j = 540 if j == 0 else e[j-1]
        opt.add(Implies(And(meet_i, meet_j, before[i][j]), 
                     s_j >= e_i + travel_time[locs[i]][locs[j]]))

# Transitivity constraints
for i in range(7):
    for j in range(7):
        if i == j:
            continue
        for k in range(7):
            if k == i or k == j:
                continue
            opt.add(Implies(And(before[i][j], before[j][k]), before[i][k]))

# Maximize the number of friends met
total_meet = Sum([If(m, 1, 0) for m in meet])
opt.maximize(total_meet)

# Solve the problem
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for idx, (name, _, _, _, _) in enumerate(friends):
        if m.eval(meet[idx]):
            start_min = m.eval(s[idx]).as_long()
            end_min = m.eval(e[idx]).as_long()
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")