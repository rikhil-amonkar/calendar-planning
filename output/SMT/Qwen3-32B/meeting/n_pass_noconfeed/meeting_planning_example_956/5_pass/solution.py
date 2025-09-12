from z3 import Solver, Int, Function, IntSort, Distinct, sat, print

num_locations = 11

# Travel time matrix (as provided)
travel_time = [
    [0, 15, 20, 10, 25, 30, 12, 18, 22, 28, 35],
    [15, 0, 25, 10, 10, 20, 22, 18, 15, 28, 30],
    [20, 25, 0, 15, 30, 25, 20, 22, 18, 10, 15],
    [10, 10, 15, 0, 20, 25, 12, 18, 22, 28, 35],
    [25, 10, 30, 20, 0, 10, 22, 18, 15, 28, 30],
    [30, 20, 25, 25, 10, 0, 20, 22, 18, 10, 15],
    [12, 22, 20, 12, 22, 20, 0, 18, 22, 28, 35],
    [18, 18, 22, 18, 18, 22, 18, 0, 15, 28, 30],
    [22, 15, 18, 22, 15, 18, 22, 15, 0, 10, 15],
    [28, 28, 10, 28, 28, 10, 28, 28, 10, 0, 15],
    [35, 30, 15, 35, 30, 15, 35, 30, 15, 15, 0]
]

# Initialize solver
solver = Solver()

# Define a function to represent travel time between two locations
travel_time_func = Function('travel_time', IntSort(), IntSort(), IntSort())

# Add constraints to define the travel time function
for i in range(num_locations):
    for j in range(num_locations):
        solver.add(travel_time_func(i, j) == travel_time[i][j])

# Define path: a permutation of locations starting with Castro (0)
path = [Int(f'path_{i}') for i in range(num_locations)]
solver.add(path[0] == 0)  # First location is Castro
solver.add(Distinct(path))  # All locations must be unique

# Define start time for each location
start_time = [Int(f'start_time_{i}') for i in range(num_locations)]
solver.add(start_time[0] == 540)  # Start at 9:00 AM (540 minutes)

# Add constraints for each consecutive pair in the path
for i in range(num_locations - 1):
    current = path[i]
    next_loc = path[i + 1]
    solver.add(start_time[next_loc] >= start_time[current] + travel_time_func(current, next_loc))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    print("Valid Plan Found:")
    print("Path:", [model.eval(path[i]) for i in range(num_locations)])
    print("Start Times:", [model.eval(start_time[i]) for i in range(num_locations)])
else:
    print("No valid plan found.")