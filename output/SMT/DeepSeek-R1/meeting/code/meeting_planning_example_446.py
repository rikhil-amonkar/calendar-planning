from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('RD', 'MD'): 9,
    ('RD', 'C'): 20,
    ('RD', 'FD'): 22,
    ('RD', 'BV'): 26,
    ('RD', 'US'): 21,
    ('MD', 'RD'): 11,
    ('MD', 'C'): 16,
    ('MD', 'FD'): 17,
    ('MD', 'BV'): 27,
    ('MD', 'US'): 16,
    ('C', 'RD'): 20,
    ('C', 'MD'): 12,
    ('C', 'FD'): 5,
    ('C', 'BV'): 22,
    ('C', 'US'): 7,
    ('FD', 'RD'): 21,
    ('FD', 'MD'): 15,
    ('FD', 'C'): 5,
    ('FD', 'BV'): 19,
    ('FD', 'US'): 9,
    ('BV', 'RD'): 25,
    ('BV', 'MD'): 25,
    ('BV', 'C'): 18,
    ('BV', 'FD'): 19,
    ('BV', 'US'): 17,
    ('US', 'RD'): 20,
    ('US', 'MD'): 18,
    ('US', 'C'): 7,
    ('US', 'FD'): 9,
    ('US', 'BV'): 15,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'RD', 540, 540, 0),  # 9:00 AM
    ('Kimberly', 'MD', 795, 1005, 15),  # 1:15 PM to 4:45 PM
    ('Robert', 'C', 735, 1215, 15),     # 12:15 PM to 8:15 PM
    ('Rebecca', 'FD', 795, 1005, 75),   # 1:15 PM to 4:45 PM
    ('Margaret', 'BV', 570, 810, 30),   # 9:30 AM to 1:30 PM
    ('Kenneth', 'US', 1170, 1275, 75),  # 7:30 PM to 9:15 PM
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
    )

# Pairwise constraints for travel times
for i in range(len(friends)):
    name_i, loc_i, _, _, _ = friends[i]
    for j in range(i + 1, len(friends)):
        name_j, loc_j, _, _, _ = friends[j]
        solver.add(Implies(And(visited[name_i], visited[name_j]),
            Or(
                arrival[name_j] >= end[name_i] + travel_time[(loc_i, loc_j)],
                arrival[name_i] >= end[name_j] + travel_time[(loc_j, loc_i)]
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