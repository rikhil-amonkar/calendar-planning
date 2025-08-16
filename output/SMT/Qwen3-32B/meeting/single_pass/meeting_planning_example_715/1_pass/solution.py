from z3 import *
import json

# Define friends and their data
friends = [
    {
        'name': 'Amanda',
        'availability_start': 375,
        'availability_end': 660,
        'required_duration': 105,
        'location': 1
    },
    {
        'name': 'Melissa',
        'availability_start': 60,
        'availability_end': 510,
        'required_duration': 30,
        'location': 2
    },
    {
        'name': 'Jeffrey',
        'availability_start': 255,
        'availability_end': 615,
        'required_duration': 120,
        'location': 3
    },
    {
        'name': 'Matthew',
        'availability_start': 105,
        'availability_end': 285,
        'required_duration': 30,
        'location': 4
    },
    {
        'name': 'Nancy',
        'availability_start': 510,
        'availability_end': 780,
        'required_duration': 105,
        'location': 5
    },
    {
        'name': 'Karen',
        'availability_start': 540,
        'availability_end': 720,
        'required_duration': 105,
        'location': 6
    },
    {
        'name': 'Robert',
        'availability_start': 165,
        'availability_end': 540,
        'required_duration': 120,
        'location': 7
    },
    {
        'name': 'Joseph',
        'availability_start': 0,
        'availability_end': 765,
        'required_duration': 105,
        'location': 8
    }
]

# Define travel times between locations
travel_times = {
    0: {1: 11, 2: 21, 3: 19, 4: 31, 5: 11, 6: 26, 7: 19, 8: 12},
    1: {0: 10, 2: 22, 3: 10, 4: 27, 5: 7, 6: 20, 7: 15, 8: 18},
    2: {0: 20, 1: 21, 3: 24, 4: 19, 5: 16, 6: 7, 7: 8, 8: 11},
    3: {0: 17, 1: 9, 2: 27, 4: 26, 5: 12, 6: 22, 7: 21, 8: 25},
    4: {0: 32, 1: 27, 2: 19, 3: 25, 5: 23, 6: 13, 7: 16, 8: 22},
    5: {0: 11, 1: 6, 2: 16, 3: 13, 4: 22, 6: 15, 7: 10, 8: 15},
    6: {0: 25, 1: 19, 2: 7, 3: 22, 4: 14, 5: 16, 7: 11, 8: 17},
    7: {0: 17, 1: 15, 2: 8, 3: 19, 4: 16, 5: 10, 6: 10, 8: 9},
    8: {0: 11, 1: 16, 2: 13, 3: 24, 4: 23, 5: 16, 6: 17, 7: 9}
}

# Create Z3 variables
steps = 8
friend_vars = [Int(f'friend_{i}') for i in range(steps)]
start_vars = [Int(f'start_{i}') for i in range(steps)]
end_vars = [Int(f'end_{i}') for i in range(steps)]

s = Optimize()

# Constraints for each step
for i in range(steps):
    s.add(And(friend_vars[i] >= -1, friend_vars[i] <= 7))
    for j in range(len(friends)):
        friend = friends[j]
        s.add(Implies(friend_vars[i] == j, start_vars[i] >= friend['availability_start']))
        s.add(Implies(friend_vars[i] == j, end_vars[i] <= friend['availability_end']))
        s.add(Implies(friend_vars[i] == j, end_vars[i] - start_vars[i] >= friend['required_duration']))
    if i == 0:
        for j in range(len(friends)):
            friend = friends[j]
            location = friend['location']
            travel_time = travel_times[0][location]
            s.add(Implies(friend_vars[i] == j, start_vars[i] >= 30 + travel_time))
    else:
        prev_friend = friend_vars[i-1]
        curr_friend = friend_vars[i]
        tt_expr = 0
        for prev_j in range(len(friends)):
            for curr_j in range(len(friends)):
                prev_loc = friends[prev_j]['location']
                curr_loc = friends[curr_j]['location']
                if prev_loc in travel_times and curr_loc in travel_times[prev_loc]:
                    tt = travel_times[prev_loc][curr_loc]
                else:
                    tt = 0
                cond = And(prev_friend == prev_j, curr_friend == curr_j)
                tt_expr = If(cond, tt, tt_expr)
        s.add(Implies(And(prev_friend != -1, curr_friend != -1), start_vars[i] >= end_vars[i-1] + tt_expr))

# Ensure each friend is met at most once
for j in range(len(friends)):
    count = Sum([If(friend_vars[i] == j, 1, 0) for i in range(steps)])
    s.add(count <= 1)

# Objective: maximize the number of friends met
objective = Sum([If(friend_vars[i] != -1, 1, 0) for i in range(steps)])
s.maximize(objective)

# Solve
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(steps):
        friend_idx = m[friend_vars[i]].as_long()
        if friend_idx != -1:
            start_time = m[start_vars[i]].as_long()
            end_time = m[end_vars[i]].as_long()
            def to_time(mins_since_base):
                base_minutes = 8 * 60 + 30  # 8:30 AM
                total_minutes = base_minutes + mins_since_base
                hours = total_minutes // 60
                minutes = total_minutes % 60
                return f"{hours:02d}:{minutes:02d}"
            start_str = to_time(start_time)
            end_str = to_time(end_time)
            friend_name = friends[friend_idx]['name']
            itinerary.append({
                "action": "meet",
                "person": friend_name,
                "start_time": start_str,
                "end_time": end_str
            })
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")