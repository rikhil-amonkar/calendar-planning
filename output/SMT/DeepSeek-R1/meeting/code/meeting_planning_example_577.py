from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('HA', 'RH'): 17,
    ('HA', 'FW'): 23,
    ('HA', 'NH'): 15,
    ('HA', 'GG'): 7,
    ('HA', 'AS'): 5,
    ('HA', 'PH'): 12,
    ('RH', 'HA'): 17,
    ('RH', 'FW'): 7,
    ('RH', 'NH'): 5,
    ('RH', 'GG'): 21,
    ('RH', 'AS'): 15,
    ('RH', 'PH'): 7,
    ('FW', 'HA'): 22,
    ('FW', 'RH'): 7,
    ('FW', 'NH'): 11,
    ('FW', 'GG'): 25,
    ('FW', 'AS'): 20,
    ('FW', 'PH'): 12,
    ('NH', 'HA'): 13,
    ('NH', 'RH'): 5,
    ('NH', 'FW'): 11,
    ('NH', 'GG'): 17,
    ('NH', 'AS'): 11,
    ('NH', 'PH'): 8,
    ('GG', 'HA'): 7,
    ('GG', 'RH'): 19,
    ('GG', 'FW'): 24,
    ('GG', 'NH'): 20,
    ('GG', 'AS'): 10,
    ('GG', 'PH'): 16,
    ('AS', 'HA'): 5,
    ('AS', 'RH'): 13,
    ('AS', 'FW'): 19,
    ('AS', 'NH'): 11,
    ('AS', 'GG'): 9,
    ('AS', 'PH'): 10,
    ('PH', 'HA'): 11,
    ('PH', 'RH'): 7,
    ('PH', 'FW'): 13,
    ('PH', 'NH'): 8,
    ('PH', 'GG'): 15,
    ('PH', 'AS'): 10,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'HA', 540, 540, 0),        # 9:00 AM
    ('Stephanie', 'RH', 1200, 1245, 15),  # 8:00 PM to 8:45 PM
    ('Kevin', 'FW', 1155, 1305, 75),      # 7:15 PM to 9:45 PM
    ('Robert', 'NH', 465, 630, 90),       # 7:45 AM to 10:30 AM
    ('Steven', 'GG', 510, 1020, 75),     # 8:30 AM to 5:00 PM
    ('Anthony', 'AS', 465, 1185, 15),     # 7:45 AM to 7:45 PM
    ('Sandra', 'PH', 885, 1305, 45),      # 2:45 PM to 9:45 PM
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