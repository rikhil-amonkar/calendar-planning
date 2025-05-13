from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('PR', 'MR'): 11,
    ('PR', 'TC'): 21,
    ('PR', 'FW'): 19,
    ('PR', 'BV'): 31,
    ('PR', 'PH'): 11,
    ('PR', 'MD'): 26,
    ('PR', 'AS'): 19,
    ('PR', 'GG'): 12,
    ('MR', 'PR'): 10,
    ('MR', 'TC'): 22,
    ('MR', 'FW'): 10,
    ('MR', 'BV'): 27,
    ('MR', 'PH'): 7,
    ('MR', 'MD'): 20,
    ('MR', 'AS'): 15,
    ('MR', 'GG'): 18,
    ('TC', 'PR'): 20,
    ('TC', 'MR'): 21,
    ('TC', 'FW'): 24,
    ('TC', 'BV'): 19,
    ('TC', 'PH'): 16,
    ('TC', 'MD'): 7,
    ('TC', 'AS'): 8,
    ('TC', 'GG'): 11,
    ('FW', 'PR'): 17,
    ('FW', 'MR'): 9,
    ('FW', 'TC'): 27,
    ('FW', 'BV'): 26,
    ('FW', 'PH'): 12,
    ('FW', 'MD'): 22,
    ('FW', 'AS'): 21,
    ('FW', 'GG'): 25,
    ('BV', 'PR'): 32,
    ('BV', 'MR'): 27,
    ('BV', 'TC'): 19,
    ('BV', 'FW'): 25,
    ('BV', 'PH'): 23,
    ('BV', 'MD'): 13,
    ('BV', 'AS'): 16,
    ('BV', 'GG'): 22,
    ('PH', 'PR'): 11,
    ('PH', 'MR'): 6,
    ('PH', 'TC'): 16,
    ('PH', 'FW'): 13,
    ('PH', 'BV'): 22,
    ('PH', 'MD'): 15,
    ('PH', 'AS'): 10,
    ('PH', 'GG'): 15,
    ('MD', 'PR'): 25,
    ('MD', 'MR'): 19,
    ('MD', 'TC'): 7,
    ('MD', 'FW'): 22,
    ('MD', 'BV'): 14,
    ('MD', 'PH'): 16,
    ('MD', 'AS'): 11,
    ('MD', 'GG'): 17,
    ('AS', 'PR'): 17,
    ('AS', 'MR'): 15,
    ('AS', 'TC'): 8,
    ('AS', 'FW'): 19,
    ('AS', 'BV'): 16,
    ('AS', 'PH'): 10,
    ('AS', 'MD'): 10,
    ('AS', 'GG'): 9,
    ('GG', 'PR'): 11,
    ('GG', 'MR'): 16,
    ('GG', 'TC'): 13,
    ('GG', 'FW'): 24,
    ('GG', 'BV'): 23,
    ('GG', 'PH'): 16,
    ('GG', 'MD'): 17,
    ('GG', 'AS'): 9,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'PR', 540, 540, 0),       # 9:00 AM
    ('Amanda', 'MR', 885, 1110, 105),    # 2:45 PM to 7:30 PM
    ('Melissa', 'TC', 570, 1020, 30),    # 9:30 AM to 5:00 PM
    ('Jeffrey', 'FW', 765, 1125, 120),   # 12:45 PM to 6:45 PM
    ('Matthew', 'BV', 615, 795, 30),     # 10:15 AM to 1:15 PM
    ('Nancy', 'PH', 1020, 1290, 105),    # 5:00 PM to 9:30 PM
    ('Karen', 'MD', 1050, 1230, 105),    # 5:30 PM to 8:30 PM
    ('Robert', 'AS', 675, 1050, 120),    # 11:15 AM to 5:30 PM
    ('Joseph', 'GG', 510, 1305, 105),    # 8:30 AM to 9:15 PM
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