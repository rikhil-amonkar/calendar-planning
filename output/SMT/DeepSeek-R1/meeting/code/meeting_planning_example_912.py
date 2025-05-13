from z3 import *

# Define travel times between locations (in minutes)
travel_time = {
    ('US', 'P'): 24,
    ('US', 'A'): 15,
    ('US', 'M'): 18,
    ('US', 'F'): 9,
    ('US', 'N'): 9,
    ('US', 'S'): 27,
    ('US', 'C'): 7,
    ('US', 'R'): 13,
    ('US', 'NB'): 10,
    ('US', 'H'): 18,
    ('P', 'US'): 22,
    ('P', 'A'): 19,
    ('P', 'M'): 11,
    ('P', 'F'): 23,
    ('P', 'N'): 18,
    ('P', 'S'): 15,
    ('P', 'C'): 21,
    ('P', 'R'): 14,
    ('P', 'NB'): 18,
    ('P', 'H'): 15,
    ('A', 'US'): 14,
    ('A', 'P'): 17,
    ('A', 'M'): 15,
    ('A', 'F'): 17,
    ('A', 'N'): 11,
    ('A', 'S'): 16,
    ('A', 'C'): 15,
    ('A', 'R'): 13,
    ('A', 'NB'): 15,
    ('A', 'H'): 5,
    ('M', 'US'): 16,
    ('M', 'P'): 10,
    ('M', 'A'): 15,
    ('M', 'F'): 17,
    ('M', 'N'): 12,
    ('M', 'S'): 19,
    ('M', 'C'): 15,
    ('M', 'R'): 8,
    ('M', 'NB'): 11,
    ('M', 'H'): 16,
    ('F', 'US'): 9,
    ('F', 'P'): 22,
    ('F', 'A'): 17,
    ('F', 'M'): 15,
    ('F', 'N'): 8,
    ('F', 'S'): 30,
    ('F', 'C'): 5,
    ('F', 'R'): 11,
    ('F', 'NB'): 7,
    ('F', 'H'): 19,
    ('N', 'US'): 7,
    ('N', 'P'): 17,
    ('N', 'A'): 11,
    ('N', 'M'): 11,
    ('N', 'F'): 9,
    ('N', 'S'): 24,
    ('N', 'C'): 6,
    ('N', 'R'): 5,
    ('N', 'NB'): 8,
    ('N', 'H'): 13,
    ('S', 'US'): 30,
    ('S', 'P'): 16,
    ('S', 'A'): 17,
    ('S', 'M'): 21,
    ('S', 'F'): 30,
    ('S', 'N'): 27,
    ('S', 'C'): 30,
    ('S', 'R'): 24,
    ('S', 'NB'): 28,
    ('S', 'H'): 15,
    ('C', 'US'): 7,
    ('C', 'P'): 19,
    ('C', 'A'): 17,
    ('C', 'M'): 12,
    ('C', 'F'): 5,
    ('C', 'N'): 9,
    ('C', 'S'): 29,
    ('C', 'R'): 7,
    ('C', 'NB'): 3,
    ('C', 'H'): 19,
    ('R', 'US'): 10,
    ('R', 'P'): 14,
    ('R', 'A'): 15,
    ('R', 'M'): 7,
    ('R', 'F'): 11,
    ('R', 'N'): 5,
    ('R', 'S'): 23,
    ('R', 'C'): 9,
    ('R', 'NB'): 5,
    ('R', 'H'): 17,
    ('NB', 'US'): 7,
    ('NB', 'P'): 17,
    ('NB', 'A'): 16,
    ('NB', 'M'): 9,
    ('NB', 'F'): 8,
    ('NB', 'N'): 7,
    ('NB', 'S'): 27,
    ('NB', 'C'): 6,
    ('NB', 'R'): 4,
    ('NB', 'H'): 18,
    ('H', 'US'): 19,
    ('H', 'P'): 15,
    ('H', 'A'): 5,
    ('H', 'M'): 17,
    ('H', 'F'): 21,
    ('H', 'N'): 15,
    ('H', 'S'): 15,
    ('H', 'C'): 19,
    ('H', 'R'): 17,
    ('H', 'NB'): 19,
}

# Friends data including a dummy for the starting point
friends = [
    ('Dummy', 'US', 540, 540, 0),
    ('Kimberly', 'P', 930, 960, 15),
    ('Elizabeth', 'A', 1155, 1215, 15),
    ('Joshua', 'M', 630, 855, 45),
    ('Sandra', 'F', 1170, 1215, 45),
    ('Kenneth', 'N', 765, 1305, 30),
    ('Betty', 'S', 840, 1140, 60),
    ('Deborah', 'C', 1035, 1230, 15),
    ('Barbara', 'R', 1050, 1275, 120),
    ('Steven', 'NB', 1065, 1230, 90),
    ('Daniel', 'H', 1110, 1125, 15),
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