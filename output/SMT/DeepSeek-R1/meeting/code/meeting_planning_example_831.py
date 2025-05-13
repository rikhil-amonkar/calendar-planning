from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('PR', 'FW'): 19,
    ('PR', 'AS'): 19,
    ('PR', 'FD'): 23,
    ('PR', 'US'): 22,
    ('PR', 'SS'): 15,
    ('PR', 'EB'): 20,
    ('PR', 'GG'): 12,
    ('PR', 'CH'): 21,
    ('PR', 'RD'): 7,
    ('FW', 'PR'): 17,
    ('FW', 'AS'): 21,
    ('FW', 'FD'): 11,
    ('FW', 'US'): 13,
    ('FW', 'SS'): 27,
    ('FW', 'EB'): 8,
    ('FW', 'GG'): 25,
    ('FW', 'CH'): 12,
    ('FW', 'RD'): 18,
    ('AS', 'PR'): 17,
    ('AS', 'FW'): 19,
    ('AS', 'FD'): 17,
    ('AS', 'US'): 14,
    ('AS', 'SS'): 16,
    ('AS', 'EB'): 16,
    ('AS', 'GG'): 9,
    ('AS', 'CH'): 15,
    ('AS', 'RD'): 11,
    ('FD', 'PR'): 22,
    ('FD', 'FW'): 10,
    ('FD', 'AS'): 17,
    ('FD', 'US'): 9,
    ('FD', 'SS'): 30,
    ('FD', 'EB'): 4,
    ('FD', 'GG'): 23,
    ('FD', 'CH'): 5,
    ('FD', 'RD'): 21,
    ('US', 'PR'): 24,
    ('US', 'FW'): 15,
    ('US', 'AS'): 15,
    ('US', 'FD'): 9,
    ('US', 'SS'): 27,
    ('US', 'EB'): 11,
    ('US', 'GG'): 22,
    ('US', 'CH'): 7,
    ('US', 'RD'): 20,
    ('SS', 'PR'): 16,
    ('SS', 'FW'): 29,
    ('SS', 'AS'): 17,
    ('SS', 'FD'): 30,
    ('SS', 'US'): 30,
    ('SS', 'EB'): 30,
    ('SS', 'GG'): 11,
    ('SS', 'CH'): 30,
    ('SS', 'RD'): 12,
    ('EB', 'PR'): 20,
    ('EB', 'FW'): 6,
    ('EB', 'AS'): 19,
    ('EB', 'FD'): 5,
    ('EB', 'US'): 10,
    ('EB', 'SS'): 30,
    ('EB', 'GG'): 25,
    ('EB', 'CH'): 7,
    ('EB', 'RD'): 21,
    ('GG', 'PR'): 11,
    ('GG', 'FW'): 24,
    ('GG', 'AS'): 9,
    ('GG', 'FD'): 26,
    ('GG', 'US'): 22,
    ('GG', 'SS'): 10,
    ('GG', 'EB'): 25,
    ('GG', 'CH'): 23,
    ('GG', 'RD'): 7,
    ('CH', 'PR'): 19,
    ('CH', 'FW'): 8,
    ('CH', 'AS'): 17,
    ('CH', 'FD'): 5,
    ('CH', 'US'): 7,
    ('CH', 'SS'): 29,
    ('CH', 'EB'): 5,
    ('CH', 'GG'): 23,
    ('CH', 'RD'): 20,
    ('RD', 'PR'): 7,
    ('RD', 'FW'): 18,
    ('RD', 'AS'): 13,
    ('RD', 'FD'): 22,
    ('RD', 'US'): 21,
    ('RD', 'SS'): 11,
    ('RD', 'EB'): 19,
    ('RD', 'GG'): 9,
    ('RD', 'CH'): 20,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'PR', 540, 540, 0),       # 9:00 AM
    ('Jeffrey', 'FW', 615, 780, 90),     # 10:15 AM to 1:00 PM
    ('Ronald', 'AS', 465, 885, 120),     # 7:45 AM to 2:45 PM
    ('Jason', 'FD', 645, 960, 105),      # 10:45 AM to 4:00 PM
    ('Melissa', 'US', 1065, 1095, 15),   # 5:45 PM to 6:15 PM
    ('Elizabeth', 'SS', 885, 1050, 105), # 2:45 PM to 5:30 PM
    ('Margaret', 'EB', 795, 1140, 90),   # 1:15 PM to 7:00 PM
    ('George', 'GG', 1140, 1260, 75),    # 7:00 PM to 10:00 PM
    ('Richard', 'CH', 570, 1260, 15),    # 9:30 AM to 9:00 PM
    ('Laura', 'RD', 585, 1080, 60),      # 9:45 AM to 6:00 PM
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