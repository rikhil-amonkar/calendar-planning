from z3 import *

# Define travel times between locations (in minutes) using abbreviations
travel_time = {
    ('HA', 'MD'): 11,
    ('HA', 'US'): 19,
    ('HA', 'PH'): 12,
    ('HA', 'BV'): 18,
    ('HA', 'FW'): 23,
    ('HA', 'MR'): 17,
    ('HA', 'RD'): 10,
    ('HA', 'SD'): 15,
    ('HA', 'GG'): 7,
    ('MD', 'HA'): 12,
    ('MD', 'US'): 15,
    ('MD', 'PH'): 16,
    ('MD', 'BV'): 14,
    ('MD', 'FW'): 22,
    ('MD', 'MR'): 19,
    ('MD', 'RD'): 20,
    ('MD', 'SD'): 24,
    ('MD', 'GG'): 17,
    ('US', 'HA'): 18,
    ('US', 'MD'): 14,
    ('US', 'PH'): 15,
    ('US', 'BV'): 15,
    ('US', 'FW'): 15,
    ('US', 'MR'): 18,
    ('US', 'RD'): 20,
    ('US', 'SD'): 27,
    ('US', 'GG'): 22,
    ('PH', 'HA'): 11,
    ('PH', 'MD'): 15,
    ('PH', 'US'): 12,
    ('PH', 'BV'): 22,
    ('PH', 'FW'): 13,
    ('PH', 'MR'): 6,
    ('PH', 'RD'): 12,
    ('PH', 'SD'): 21,
    ('PH', 'GG'): 15,
    ('BV', 'HA'): 19,
    ('BV', 'MD'): 13,
    ('BV', 'US'): 18,
    ('BV', 'PH'): 23,
    ('BV', 'FW'): 25,
    ('BV', 'MR'): 27,
    ('BV', 'RD'): 25,
    ('BV', 'SD'): 23,
    ('BV', 'GG'): 22,
    ('FW', 'HA'): 22,
    ('FW', 'MD'): 22,
    ('FW', 'US'): 13,
    ('FW', 'PH'): 12,
    ('FW', 'BV'): 26,
    ('FW', 'MR'): 9,
    ('FW', 'RD'): 18,
    ('FW', 'SD'): 27,
    ('FW', 'GG'): 25,
    ('MR', 'HA'): 16,
    ('MR', 'MD'): 20,
    ('MR', 'US'): 16,
    ('MR', 'PH'): 7,
    ('MR', 'BV'): 27,
    ('MR', 'FW'): 10,
    ('MR', 'RD'): 11,
    ('MR', 'SD'): 19,
    ('MR', 'GG'): 18,
    ('RD', 'HA'): 10,
    ('RD', 'MD'): 20,
    ('RD', 'US'): 21,
    ('RD', 'PH'): 10,
    ('RD', 'BV'): 27,
    ('RD', 'FW'): 18,
    ('RD', 'MR'): 9,
    ('RD', 'SD'): 11,
    ('RD', 'GG'): 9,
    ('SD', 'HA'): 15,
    ('SD', 'MD'): 25,
    ('SD', 'US'): 30,
    ('SD', 'PH'): 21,
    ('SD', 'BV'): 22,
    ('SD', 'FW'): 29,
    ('SD', 'MR'): 21,
    ('SD', 'RD'): 12,
    ('SD', 'GG'): 11,
    ('GG', 'HA'): 7,
    ('GG', 'MD'): 17,
    ('GG', 'US'): 22,
    ('GG', 'PH'): 16,
    ('GG', 'BV'): 23,
    ('GG', 'FW'): 24,
    ('GG', 'MR'): 16,
    ('GG', 'RD'): 7,
    ('GG', 'SD'): 10,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'HA', 540, 540, 0),       # 9:00 AM
    ('Elizabeth', 'MD', 630, 1200, 90),  # 10:30 AM to 8:00 PM
    ('David', 'US', 975, 1140, 45),      # 3:15 PM to 7:00 PM
    ('Sandra', 'PH', 420, 1200, 120),    # 7:00 AM to 8:00 PM
    ('Thomas', 'BV', 1170, 1230, 30),    # 7:30 PM to 8:30 PM
    ('Robert', 'FW', 600, 900, 15),      # 10:00 AM to 3:00 PM
    ('Kenneth', 'MR', 645, 780, 45),     # 10:45 AM to 1:00 PM
    ('Melissa', 'RD', 1110, 1200, 15),   # 6:15 PM to 8:00 PM
    ('Kimberly', 'SD', 615, 1110, 105),  # 10:15 AM to 6:15 PM
    ('Amanda', 'GG', 465, 1110, 15),     # 7:45 AM to 6:45 PM
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