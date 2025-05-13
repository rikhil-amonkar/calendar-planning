from z3 import *

# Define travel times between locations (in minutes)
travel_time = {
    ('HA', 'F'): 23,
    ('HA', 'R'): 10,
    ('HA', 'M'): 11,
    ('HA', 'B'): 18,
    ('F', 'HA'): 22,
    ('F', 'R'): 18,
    ('F', 'M'): 22,
    ('F', 'B'): 26,
    ('R', 'HA'): 10,
    ('R', 'F'): 18,
    ('R', 'M'): 20,
    ('R', 'B'): 26,
    ('M', 'HA'): 12,
    ('M', 'F'): 22,
    ('M', 'R'): 20,
    ('M', 'B'): 15,
    ('B', 'HA'): 19,
    ('B', 'F'): 25,
    ('B', 'R'): 25,
    ('B', 'M'): 13,
}

# Friends data: (name, location, available_start, available_end, required_duration)
friends = [
    ('Sarah', 'F', 885, 1050, 105),
    ('Mary', 'R', 780, 1155, 75),
    ('Helen', 'M', 1305, 1350, 30),
    ('Thomas', 'B', 915, 1125, 120),
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
    
    # Constraints if friend is visited
    solver.add(Implies(visited[name],
        And(
            arrival[name] >= 540 + travel_time[('HA', loc)],  # Arrival after initial travel
            start[name] == If(arrival[name] >= a_start, arrival[name], a_start),
            end[name] == start[name] + dur,
            end[name] <= a_end
        )
    ))
    # Set unvisited friends' times to 0 (for clarity, though not strictly necessary)
    solver.add(Implies(Not(visited[name]), 
        And(arrival[name] == 0, start[name] == 0, end[name] == 0)
    ))

# Pairwise constraints for order and travel times
for i in range(len(friends)):
    name_i, loc_i, _, _, _ = friends[i]
    for j in range(i+1, len(friends)):
        name_j, loc_j, _, _, _ = friends[j]
        # If both are visited, enforce travel time between them
        solver.add(Implies(And(visited[name_i], visited[name_j]),
            Or(
                arrival[name_j] >= end[name_i] + travel_time[(loc_i, loc_j)],
                arrival[name_i] >= end[name_j] + travel_time[(loc_j, loc_i)]
            )
        ))

# Maximize the number of friends visited
total_visited = Sum([If(v, 1, 0) for v in visited.values()])
solver.maximize(total_visited)

# Solve and output the result
if solver.check() == sat:
    model = solver.model()
    print("Optimal schedule:")
    for name in visited:
        if model.evaluate(visited[name]):
            a = model.evaluate(arrival[name]).as_long()
            s = model.evaluate(start[name]).as_long()
            e = model.evaluate(end[name]).as_long()
            print(f"{name}: Arrive {a//60:02}:{a%60:02}, Meet {s//60:02}:{s%60:02}-{e//60:02}:{e%60:02}")
        else:
            print(f"{name}: Not visited")
else:
    print("No solution found.")