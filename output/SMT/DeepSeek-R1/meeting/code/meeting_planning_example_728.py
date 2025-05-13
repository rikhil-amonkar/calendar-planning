from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('MR', 'MS'): 20,
    ('MR', 'FW'): 10,
    ('MR', 'PR'): 10,
    ('MR', 'US'): 16,
    ('MR', 'SS'): 19,
    ('MR', 'FD'): 17,
    ('MR', 'HA'): 16,
    ('MR', 'RH'): 8,
    ('MS', 'MR'): 19,
    ('MS', 'FW'): 22,
    ('MS', 'PR'): 25,
    ('MS', 'US'): 15,
    ('MS', 'SS'): 24,
    ('MS', 'FD'): 15,
    ('MS', 'HA'): 12,
    ('MS', 'RH'): 15,
    ('FW', 'MR'): 9,
    ('FW', 'MS'): 22,
    ('FW', 'PR'): 17,
    ('FW', 'US'): 13,
    ('FW', 'SS'): 27,
    ('FW', 'FD'): 11,
    ('FW', 'HA'): 22,
    ('FW', 'RH'): 7,
    ('PR', 'MR'): 11,
    ('PR', 'MS'): 26,
    ('PR', 'FW'): 19,
    ('PR', 'US'): 22,
    ('PR', 'SS'): 15,
    ('PR', 'FD'): 23,
    ('PR', 'HA'): 15,
    ('PR', 'RH'): 14,
    ('US', 'MR'): 18,
    ('US', 'MS'): 14,
    ('US', 'FW'): 15,
    ('US', 'PR'): 24,
    ('US', 'SS'): 27,
    ('US', 'FD'): 9,
    ('US', 'HA'): 18,
    ('US', 'RH'): 13,
    ('SS', 'MR'): 21,
    ('SS', 'MS'): 25,
    ('SS', 'FW'): 29,
    ('SS', 'PR'): 16,
    ('SS', 'US'): 30,
    ('SS', 'FD'): 30,
    ('SS', 'HA'): 15,
    ('SS', 'RH'): 24,
    ('FD', 'MR'): 15,
    ('FD', 'MS'): 17,
    ('FD', 'FW'): 10,
    ('FD', 'PR'): 22,
    ('FD', 'US'): 9,
    ('FD', 'SS'): 30,
    ('FD', 'HA'): 19,
    ('FD', 'RH'): 11,
    ('HA', 'MR'): 17,
    ('HA', 'MS'): 11,
    ('HA', 'FW'): 23,
    ('HA', 'PR'): 15,
    ('HA', 'US'): 19,
    ('HA', 'SS'): 15,
    ('HA', 'FD'): 21,
    ('HA', 'RH'): 17,
    ('RH', 'MR'): 7,
    ('RH', 'MS'): 16,
    ('RH', 'FW'): 7,
    ('RH', 'PR'): 14,
    ('RH', 'US'): 10,
    ('RH', 'SS'): 23,
    ('RH', 'FD'): 11,
    ('RH', 'HA'): 17,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'MR', 540, 540, 0),       # 9:00 AM
    ('Karen', 'MS', 855, 1320, 30),      # 2:15 PM to 10:00 PM
    ('Richard', 'FW', 870, 1050, 30),     # 2:30 PM to 5:30 PM
    ('Robert', 'PR', 1305, 1365, 60),    # 9:45 PM to 10:45 PM
    ('Joseph', 'US', 705, 885, 120),     # 11:45 AM to 2:45 PM
    ('Helen', 'SS', 885, 1245, 105),     # 2:45 PM to 8:45 PM
    ('Elizabeth', 'FD', 600, 765, 75),   # 10:00 AM to 12:45 PM
    ('Kimberly', 'HA', 855, 1050, 105),  # 2:15 PM to 5:30 PM
    ('Ashley', 'RH', 690, 1290, 45),     # 11:30 AM to 9:30 PM
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