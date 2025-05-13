from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('BV', 'PH'): 23,
    ('BV', 'MD'): 13,
    ('BV', 'HA'): 19,
    ('BV', 'FD'): 19,
    ('PH', 'BV'): 22,
    ('PH', 'MD'): 15,
    ('PH', 'HA'): 11,
    ('PH', 'FD'): 13,
    ('MD', 'BV'): 15,
    ('MD', 'PH'): 16,
    ('MD', 'HA'): 12,
    ('MD', 'FD'): 17,
    ('HA', 'BV'): 18,
    ('HA', 'PH'): 12,
    ('HA', 'MD'): 11,
    ('HA', 'FD'): 21,
    ('FD', 'BV'): 19,
    ('FD', 'PH'): 13,
    ('FD', 'MD'): 17,
    ('FD', 'HA'): 19,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'BV', 540, 540, 0),      # 9:00 AM
    ('Mary', 'PH', 600, 1140, 45),     # 10:00 AM to 7:00 PM
    ('Lisa', 'MD', 1230, 1320, 75),    # 8:30 PM to 10:00 PM
    ('Betty', 'HA', 435, 1035, 90),    # 7:15 AM to 5:15 PM
    ('Charles', 'FD', 675, 900, 120),  # 11:15 AM to 3:00 PM
]

# Initialize Z3 solver and variables
solver = Optimize()
visited = {}
arrival = {}
start = {}
end = {}

for name, loc, a_start, a_end, dur in friends:
    visited[name] = Bool(f'visited_{name}')
    arrival[name] = Int(f'arrival_{name}')
    start[name] = Int(f'start_{name}')
    end[name] = Int(f'end_{name}')

# Dummy must be visited and fixed at 9:00 AM
solver.add(visited['Dummy'] == True)
solver.add(start['Dummy'] == 540)
solver.add(end['Dummy'] == 540)

# Constraints for real friends
for name, loc, a_start, a_end, dur in friends[1:]:
    solver.add(Implies(visited[name],
        And(
            start[name] == If(arrival[name] >= a_start, arrival[name], a_start),
            end[name] == start[name] + dur,
            end[name] <= a_end
        )
    ))
    solver.add(Implies(Not(visited[name]),
        And(arrival[name] == 0, start[name] == 0, end[name] == 0)
    ))

# Pairwise constraints for travel times
for i in range(len(friends)):
    name_i, loc_i, _, _, _ = friends[i]
    for j in range(i + 1, len(friends)):
        name_j, loc_j, _, _, _ = friends[j]
        tt_ij = travel_time.get((loc_i, loc_j), 0)
        tt_ji = travel_time.get((loc_j, loc_i), 0)
        solver.add(Implies(And(visited[name_i], visited[name_j]),
            Or(
                arrival[name_j] >= end[name_i] + tt_ij,
                arrival[name_i] >= end[name_j] + tt_ji
            )
        ))

# Maximize the number of real friends visited
real_friends = [name for name, _, _, _, _ in friends[1:]]
solver.maximize(Sum([If(visited[name], 1, 0) for name in real_friends]))

# Solve and output the result
if solver.check() == sat:
    model = solver.model()
    print("Optimal schedule:")
    for name in real_friends:
        if model.evaluate(visited[name]):
            a = model.evaluate(arrival[name]).as_long()
            s = model.evaluate(start[name]).as_long()
            e = model.evaluate(end[name]).as_long()
            print(f"{name}: Arrive {a//60:02}:{a%60:02}, Meet {s//60:02}:{s%60:02}-{e//60:02}:{e%60:02}")
        else:
            print(f"{name}: Not visited")
else:
    print("No solution found.")