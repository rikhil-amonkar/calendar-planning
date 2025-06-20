from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday']

# Define the start and end times
start_times = [9, 10, 11, 12, 13, 14, 15, 16]
end_times = [10, 11, 12, 13, 14, 15, 16, 17]

# Define the existing schedules for Margaret and Alexis
margaret_schedules = {
    'Monday': [10.5, 11.5, 13, 15.5],
    'Tuesday': [12, 12.5]
}
alexis_schedules = {
    'Monday': [9.5, 11.5, 12.5, 14, 17],
    'Tuesday': [9, 10, 10.5, 14, 16.5]
}

# Define the preferences for Margaret
margaret_preferences = {
    'Monday': True,
    'Tuesday': {'before': 14.5}
}

# Define the meeting duration
meeting_duration = 0.5

# Create a Z3 solver
solver = Solver()

# Declare the variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Add the constraints for the day
solver.add(day >= 0)
solver.add(day < len(days))

# Add the constraints for the start and end times
solver.add(start_time >= 9)
solver.add(start_time < 17)
solver.add(end_time > start_time)
solver.add(end_time <= 17)

# Add the constraints for the existing schedules
for day_name in days:
    for schedule in margaret_schedules[day_name]:
        solver.add(Or(start_time < schedule, end_time < schedule))
    for schedule in alexis_schedules[day_name]:
        solver.add(Or(start_time < schedule, end_time < schedule))

# Add the constraints for Margaret's preferences
if margaret_preferences['Monday']:
    solver.add(day == 0)
else:
    solver.add(day == 1)
if 'before' in margaret_preferences['Tuesday']:
    solver.add(start_time < margaret_preferences['Tuesday']['before'])

# Add the constraint for the meeting duration
solver.add(end_time - start_time == meeting_duration)

# Check the solution
if solver.check() == sat:
    model = solver.model()
    print('SOLUTION:')
    print(f'Day: {days[model[day].as_long()]}')
    print(f'Start Time: {model[start_time].as_real().as_decimal()[:5]}')
    print(f'End Time: {model[end_time].as_real().as_decimal()[:5]}')
else:
    print('No solution found')