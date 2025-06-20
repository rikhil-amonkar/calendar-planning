from z3 import *

# Define the travel distances in minutes
distances = {
    'Pacific Heights to Presidio': 11,
    'Pacific Heights to Marina District': 6,
    'Presidio to Pacific Heights': 11,
    'Presidio to Marina District': 10,
    'Marina District to Pacific Heights': 7,
    'Marina District to Presidio': 10
}

# Define the constraints
start_time = 0
end_time = 480  # 10 hours
jason_start_time = 600  # 10:00 AM
jason_end_time = 765  # 4:15 PM
jason_meeting_duration = 90
kenneth_start_time = 1980  # 3:30 PM
kenneth_end_time = 2250  # 4:45 PM
kenneth_meeting_duration = 45

# Define the variables
x1, x2, x3 = Ints('x1 x2 x3')

# Define the constraints
constraints = [
    x1 >= 0,
    x1 <= end_time,
    x2 >= 0,
    x2 <= end_time,
    x3 >= 0,
    x3 <= end_time,
    x1 + distances['Pacific Heights to Presidio'] <= jason_start_time,
    x2 + distances['Pacific Heights to Marina District'] <= kenneth_start_time,
    x3 + distances['Presidio to Marina District'] <= kenneth_start_time,
    jason_start_time + jason_meeting_duration <= x1 + distances['Pacific Heights to Presidio'],
    kenneth_start_time + kenneth_meeting_duration <= x2 + distances['Pacific Heights to Marina District'],
    kenneth_start_time + kenneth_meeting_duration <= x3 + distances['Presidio to Marina District'],
    jason_start_time + jason_meeting_duration >= x1,
    kenneth_start_time + kenneth_meeting_duration >= x2,
    kenneth_start_time + kenneth_meeting_duration >= x3,
]

# Define the objective function
objective_function = [x1 + x2 + x3]

# Solve the problem
solver = Optimize()
solver.add(constraints)
solver.add(Maximize(sum(objective_function)))

# Check if the solver found a solution
if solver.check() == sat:
    model = solver.model()
    print(f"Optimal schedule: Pacific Heights at {model[x1]} minutes, Presidio at {model[x2]} minutes, Marina District at {model[x3]} minutes")
else:
    print("No solution found")

# Print the optimal schedule
print("SOLUTION:")
print(f"Pacific Heights at {model[x1]} minutes, Presidio at {model[x2]} minutes, Marina District at {model[x3]} minutes")