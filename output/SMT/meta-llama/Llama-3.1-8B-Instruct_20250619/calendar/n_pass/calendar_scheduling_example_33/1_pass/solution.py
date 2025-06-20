from z3 import *

# Define the day of the week (Monday = 0, Sunday = 6)
day_of_week = [0]

# Define the start and end times (9:00 to 17:00)
start_time = 9
end_time = 17

# Define the duration of the meeting (30 minutes)
meeting_duration = 30

# Define the schedules for each participant
schedules = {
    'Lisa': [(9, 10), (10.5, 11.5), (12.5, 13), (16, 16.5)],
    'Bobby': [(9, 9.5), (10, 10.5), (11.5, 12), (15, 15.5)],
    'Randy': [(9.5, 10), (10.5, 11), (11.5, 12.5), (13, 13.5), (14.5, 15.5), (16, 16.5)]
}

# Define the preferences for Bobby (avoid meetings after 15:00)
bobby_preferences = [(15, 17)]

# Create a Z3 solver
solver = Solver()

# Define the variables for the start and end times of the meeting
day = Int('day')
start_time_var = Int('start_time')
end_time_var = Int('end_time')

# Add constraints for the day of the week
solver.add(day == 0)

# Add constraints for the start and end times
solver.add(start_time_var >= start_time)
solver.add(end_time_var <= end_time)
solver.add(end_time_var - start_time_var == meeting_duration)

# Add constraints for the schedules of each participant
for participant, participant_schedule in schedules.items():
    for start, end in participant_schedule:
        solver.add(start_time_var >= start)
        solver.add(end_time_var <= end)

# Add constraints for Bobby's preferences
for start, end in bobby_preferences:
    solver.add(end_time_var <= start)

# Check if there is a solution
if solver.check() == sat:
    # Get the values of the variables
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time_var].as_long() / 60
    end_time_value = model[end_time_var].as_long() / 60

    # Print the solution
    print('SOLUTION:')
    print(f'Day: {day_of_week[day_value]}')
    print(f'Start Time: {int(start_time_value):02d}:{int((start_time_value - int(start_time_value)) * 60):02d}')
    print(f'End Time: {int(end_time_value):02d}:{int((end_time_value - int(end_time_value)) * 60):02d}')
else:
    print('No solution found')