from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('PR', 'RD'): 7,
    ('PR', 'NB'): 18,
    ('PR', 'FD'): 23,
    ('PR', 'GG'): 12,
    ('PR', 'US'): 22,
    ('RD', 'PR'): 7,
    ('RD', 'NB'): 17,
    ('RD', 'FD'): 22,
    ('RD', 'GG'): 9,
    ('RD', 'US'): 21,
    ('NB', 'PR'): 17,
    ('NB', 'RD'): 18,
    ('NB', 'FD'): 8,
    ('NB', 'GG'): 22,
    ('NB', 'US'): 7,
    ('FD', 'PR'): 22,
    ('FD', 'RD'): 21,
    ('FD', 'NB'): 7,
    ('FD', 'GG'): 23,
    ('FD', 'US'): 9,
    ('GG', 'PR'): 11,
    ('GG', 'RD'): 7,
    ('GG', 'NB'): 24,
    ('GG', 'FD'): 26,
    ('GG', 'US'): 22,
    ('US', 'PR'): 24,
    ('US', 'RD'): 20,
    ('US', 'NB'): 10,
    ('US', 'FD'): 9,
    ('US', 'GG'): 22,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'PR', 540, 540, 0),       # 9:00 AM
    ('Jason', 'RD', 780, 1185, 90),      # 1:00 PM to 8:45 PM
    ('Melissa', 'NB', 1125, 1215, 45),   # 6:45 PM to 8:15 PM
    ('Brian', 'FD', 585, 1305, 15),      # 9:45 AM to 9:45 PM
    ('Elizabeth', 'GG', 525, 1290, 105), # 8:45 AM to 9:30 PM
    ('Laura', 'US', 855, 1170, 75),      # 2:15 PM to 7:30 PM
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