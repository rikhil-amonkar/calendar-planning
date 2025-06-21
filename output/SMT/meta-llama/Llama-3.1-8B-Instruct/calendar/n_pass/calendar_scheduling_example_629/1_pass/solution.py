from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday']

# Define the start and end times of the work hours
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
meeting_duration = 30  # half an hour in minutes

# Define the existing schedules for Margaret and Alexis
margaret_schedule = {
    'Monday': [10 * 60 + 30, 11 * 60, 13 * 60, 15 * 60],
    'Tuesday': [12 * 60, 12 * 60 + 30]
}

alexis_schedule = {
    'Monday': [9 * 60 + 30, 11 * 60 + 30, 12 * 60 + 30, 14 * 60, 17 * 60],
    'Tuesday': [9 * 60, 10 * 60, 14 * 60, 16 * 30]
}

# Define the preferences for Margaret
margaret_preferences = {
    'Monday': False,
    'Tuesday': {'before': 14 * 60 + 30}
}

# Create a Z3 solver
solver = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time_var = [Int(f'start_time_{i}') for i in range(len(days))]
end_time_var = [Int(f'end_time_{i}') for i in range(len(days))]

# Add constraints
for i, day_name in enumerate(days):
    solver.add(day[i] == margaret_preferences[day_name]['Monday'])
    solver.add(start_time_var[i] >= start_time)
    solver.add(start_time_var[i] <= end_time - meeting_duration)
    solver.add(end_time_var[i] >= start_time_var[i] + meeting_duration)
    solver.add(end_time_var[i] <= end_time)

    # Check if the meeting time conflicts with Margaret's schedule
    for time in margaret_schedule[day_name]:
        solver.add(start_time_var[i] > time)
        solver.add(end_time_var[i] < time)

    # Check if the meeting time conflicts with Alexis's schedule
    for time in alexis_schedule[day_name]:
        solver.add(start_time_var[i] > time)
        solver.add(end_time_var[i] < time)

    # Check if the meeting time satisfies Margaret's preferences
    if day_name == 'Monday':
        solver.add(start_time_var[i] > 11 * 60 + 30)
    elif day_name == 'Tuesday':
        solver.add(start_time_var[i] >= 14 * 60 + 30)

# Check if there is a solution
if solver.check() == sat:
    # Get the model
    model = solver.model()

    # Extract the values from the model
    day_value = [model.evaluate(day[i]).as_bool() for i in range(len(days))]
    start_time_value = [model.evaluate(start_time_var[i]).as_int() for i in range(len(days))]
    end_time_value = [model.evaluate(end_time_var[i]).as_int() for i in range(len(days))]

    # Print the solution
    day_name = [days[i] for i in range(len(days)) if day_value[i]]
    print(f'SOLUTION:')
    print(f'Day: {day_name[0]}')
    print(f'Start Time: {start_time_value[0] // 60:02d}:{start_time_value[0] % 60:02d}')
    print(f'End Time: {end_time_value[0] // 60:02d}:{end_time_value[0] % 60:02d}')
else:
    print('No solution found')