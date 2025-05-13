from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('FD', 'RH'): 10,
    ('FD', 'SD'): 31,
    ('FD', 'NB'): 7,
    ('FD', 'CT'): 23,
    ('FD', 'GG'): 23,
    ('RH', 'FD'): 11,
    ('RH', 'SD'): 23,
    ('RH', 'NB'): 5,
    ('RH', 'CT'): 21,
    ('RH', 'GG'): 21,
    ('SD', 'FD'): 30,
    ('SD', 'RH'): 24,
    ('SD', 'NB'): 29,
    ('SD', 'CT'): 17,
    ('SD', 'GG'): 11,
    ('NB', 'FD'): 8,
    ('NB', 'RH'): 4,
    ('NB', 'SD'): 27,
    ('NB', 'CT'): 22,
    ('NB', 'GG'): 22,
    ('CT', 'FD'): 20,
    ('CT', 'RH'): 18,
    ('CT', 'SD'): 17,
    ('CT', 'NB'): 20,
    ('CT', 'GG'): 11,
    ('GG', 'FD'): 26,
    ('GG', 'RH'): 19,
    ('GG', 'SD'): 10,
    ('GG', 'NB'): 24,
    ('GG', 'CT'): 13,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'FD', 540, 540, 0),     # 9:00 AM
    ('Ronald', 'RH', 825, 1035, 105),  # 1:45 PM to 5:15 PM (105 min)
    ('Patricia', 'SD', 555, 1320, 60), # 9:15 AM to 10:00 PM (60 min)
    ('Laura', 'NB', 750, 765, 15),     # 12:30 PM to 12:45 PM (15 min)
    ('Emily', 'CT', 975, 1110, 60),    # 4:15 PM to 6:30 PM (60 min)
    ('Mary', 'GG', 900, 990, 60),      # 3:00 PM to 4:30 PM (60 min)
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