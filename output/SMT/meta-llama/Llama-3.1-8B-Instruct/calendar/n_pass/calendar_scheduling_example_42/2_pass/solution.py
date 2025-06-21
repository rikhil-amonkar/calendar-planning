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

# Try all possible start times
for start_time_value in range(start_time, end_time - meeting_duration + 1):
    # Assume that the current start time is a solution
    solver.push()
    solver.add(start_time_var == start_time_value)
    
    # Check if the current start time is a solution
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        
        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}')
        print(f'End Time: {(start_time_value // 60 + 1) * 60 + (start_time_value % 60):02d}:{(start_time_value // 60 + 1) * 60 + (start_time_value % 60) % 60:02d}')
        
        # Exit the solver
        solver.pop()
        break
    else:
        # Exit the solver
        solver.pop()

else:
    print('No solution found')