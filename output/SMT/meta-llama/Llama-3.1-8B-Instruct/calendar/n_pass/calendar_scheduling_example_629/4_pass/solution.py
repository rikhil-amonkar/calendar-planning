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
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Add the constraints for the day
solver.add(day >= 0)
solver.add(day < len(days))

# Add the constraints for the start and end times
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(end_hour > start_hour)
solver.add(end_hour <= 17)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)
solver.add(end_minute > start_minute)
solver.add(end_minute <= 60)

# Add the constraints for the existing schedules
for day_name in days:
    for schedule in margaret_schedules[day_name]:
        solver.add(Or((start_hour < schedule/1) & (end_hour > schedule/1), (start_hour < schedule/1 + 0.5) & (end_hour > schedule/1 + 0.5)))
    for schedule in alexis_schedules[day_name]:
        solver.add(Or((start_hour < schedule/1) & (end_hour > schedule/1), (start_hour < schedule/1 + 0.5) & (end_hour > schedule/1 + 0.5)))

# Add the constraints for Margaret's preferences
if margaret_preferences['Monday']:
    solver.add(day == 0)
else:
    solver.add(day == 1)
if 'before' in margaret_preferences['Tuesday']:
    solver.add(start_hour < margaret_preferences['Tuesday']['before'] // 1)

# Add the constraint for the meeting duration
solver.add((end_hour * 60 + end_minute) - (start_hour * 60 + start_minute) == 30)

# Add the constraint that Margaret does not want to meet on Monday
if margaret_preferences['Monday']:
    solver.add(day == 0)

# Add the constraint that Margaret does not want to meet on Tuesday before 14:30
if 'before' in margaret_preferences['Tuesday']:
    solver.add(start_hour < 14)

# Check the solution
if solver.check() == sat:
    model = solver.model()
    print('SOLUTION:')
    print(f'Day: {days[model[day].as_long()]}')
    print(f'Start Time: {model[start_hour].as_long()}:{model[start_minute].as_long():02d}')
    print(f'End Time: {model[end_hour].as_long()}:{model[end_minute].as_long():02d}')
else:
    print('No solution found')