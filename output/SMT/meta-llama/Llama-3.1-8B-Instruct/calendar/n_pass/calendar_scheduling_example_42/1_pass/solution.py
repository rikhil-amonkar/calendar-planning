from z3 import *

# Define the day
day = 'Monday'

# Define the start and end times of the work hours
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes

# Define the meeting duration
meeting_duration = 60  # 1 hour in minutes

# Define the existing schedules for each participant
schedules = {
    'Julie': [9 * 60, 9 * 60 + 30, 11 * 60, 11 * 60 + 30, 12 * 60, 12 * 60 + 30, 13 * 60 + 30, 14 * 60, 16 * 60],
    'Sean': [9 * 60, 9 * 60 + 30, 13 * 60, 13 * 60 + 30, 15 * 60, 15 * 60 + 30, 16 * 60, 16 * 60 + 30],
    'Lori': [10 * 60, 10 * 60 + 30, 11 * 60, 13 * 60, 15 * 60 + 30, 17 * 60]
}

# Create a Z3 solver
solver = Solver()

# Create variables for the start time of the meeting
start_time_var = Int('start_time')

# Add constraints for each participant
for participant, schedule in schedules.items():
    for time in schedule:
        # Add a constraint that the meeting cannot start during the participant's busy time
        solver.add(start_time_var + meeting_duration > time)

# Add constraints for the start and end times
solver.add(start_time_var >= start_time)
solver.add(start_time_var + meeting_duration <= end_time)

# Check if there is a solution
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    start_time_value = model[start_time_var].as_long()
    end_time_value = start_time_value + meeting_duration

    # Print the solution
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}')
    print(f'End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}')
else:
    print('No solution found')