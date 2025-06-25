from z3 import *

# Define the travel times
travel_times = {
    'Nob Hill to Presidio': 17,
    'Presidio to Nob Hill': 18
}

# Define the constraints
start_time = 9 * 60  # 9:00 AM in minutes
robert_available = [11 * 60 + 15, 12 * 60 + 45, 13 * 60 + 15, 14 * 60 + 45, 15 * 60 + 15, 16 * 60 + 45, 5 * 60 + 45]
min_meeting_time = 120

# Define the variables
meeting_times = [Bool(f'meeting_at_{i}') for i in range(len(robert_available))]

# Create the Z3 solver
solver = Solver()

# Add the constraints
for i, meeting_time in enumerate(meeting_times):
    solver.add(meeting_time == False)  # Initially, assume no meeting
    if i == 0:
        solver.add(And(meeting_time, start_time + travel_times['Nob Hill to Presidio'] <= robert_available[i]))
    else:
        solver.add(And(meeting_time, (robert_available[i-1] + travel_times['Presidio to Nob Hill']) + travel_times['Nob Hill to Presidio'] <= robert_available[i]))

# Add the objective function
solver.add(If(Or(*meeting_times), Sum([If(meeting_time, robert_available[i] - (start_time + travel_times['Nob Hill to Presidio']), 0) for i, meeting_time in enumerate(meeting_times)]), 0) >= min_meeting_time)

# Solve the problem
solver.check()

# Get the model
model = solver.model()

# Print the solution
print("Optimal Schedule:")
for i, meeting_time in enumerate(meeting_times):
    if model.evaluate(meeting_time):
        print(f"Meet Robert at {robert_available[i]}")