from z3 import *

# Define the day of the week (Monday)
day = 0

# Define the start and end time of the work hours (9:00 to 17:00)
start_time = 9 * 60
end_time = 17 * 60

# Define the duration of the meeting (half an hour)
duration = 30

# Define the existing schedules for each participant
schedules = {
    'Joe': [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60)],
    'Keith': [(11 * 60 + 30, 12 * 60), (15 * 60, 15 * 60 + 30)],
    'Patricia': [(9 * 60, 9 * 60 + 30), (13 * 60, 13 * 60 + 30)],
    'Nancy': [(9 * 60, 11 * 60), (11 * 60 + 30, 16 * 60 + 30)],
    'Pamela': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30),
               (13 * 60, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60),
               (16 * 60 + 30, 17 * 60)]
}

# Create a Z3 solver
solver = Solver()

# Define the start time of the meeting as a variable
start_var = Int('start')

# Add constraints to the solver
for participant, schedule in schedules.items():
    for start, end in schedule:
        # Add constraint: meeting time does not conflict with participant's schedule
        solver.add(Or(start + 30 > start_var, start_var + 30 * 60 >= end))

# Add constraints: meeting time is within work hours
solver.add(And(start_var >= start_time, start_var + 30 * 60 <= end_time))

# Check if a solution exists
if solver.check() == sat:
    # Get the model
    model = solver.model()

    # Print the solution
    print('SOLUTION:')
    print(f'Day: Monday')
    print(f'Start Time: {model[start_var] // 60:02d}:{model[start_var] % 60:02d}')
    print(f'End Time: {(model[start_var] + 30 * 60) // 60:02d}:{(model[start_var] + 30 * 60) % 60:02d}')
else:
    print('No solution exists.')