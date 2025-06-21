from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday']

# Define the start and end times of the work hours
start_time = 9
end_time = 17

# Define the duration of the meeting
meeting_duration = 30

# Define the existing schedules for John and Jennifer
john_schedule = []
jennifer_schedule = {
    'Monday': [(9, 11), (11.5, 13), (13.5, 14.5), (15, 17)],
    'Tuesday': [(9, 11.5), (12, 17)],
    'Wednesday': [(9, 11.5), (12, 12.5), (13, 14), (14.5, 16), (17, 17)]
}

# Define John's preferences
john_preferences = {
    'Monday': [(14.5, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 17)]
}

# Define the solver
solver = Optimize()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time_var = [Real(f'start_time_{i}') for i in range(len(days))]
end_time_var = [Real(f'end_time_{i}') for i in range(len(days))]

# Add constraints for each day
for i, day_name in enumerate(days):
    # John has no meetings the whole week
    solver.add(Not(day[i]))

    # Jennifer has meetings on certain days and times
    if day_name in jennifer_schedule:
        for start, end in jennifer_schedule[day_name]:
            solver.add(And(start_time_var[i] > start, end_time_var[i] < end))

    # John would like to avoid more meetings on Monday after 14:30, Tuesday, Wednesday
    if day_name in john_preferences:
        for start, end in john_preferences[day_name]:
            solver.add(And(start_time_var[i] > start, end_time_var[i] < end))

    # Meeting duration
    solver.add(end_time_var[i] - start_time_var[i] == meeting_duration)

    # Start time must be between 9:00 and 17:00
    solver.add(And(start_time_var[i] >= start_time, start_time_var[i] <= end_time))

    # End time must be between 9:00 and 17:00
    solver.add(And(end_time_var[i] >= start_time, end_time_var[i] <= end_time))

# Solve the optimization problem
solver.check()

# Get the solution
model = solver.model()

# Print the solution
solution = f"SOLUTION:\nDay: {days[model.evaluate(day[0]).as_long()]}\nStart Time: {str(int(model.evaluate(start_time_var[0]).as_real().as_long() / 1)).zfill(2)}:{str(int(model.evaluate(start_time_var[0]).as_real().as_long() % 1 * 60)).zfill(2)}\nEnd Time: {str(int(model.evaluate(end_time_var[0]).as_real().as_long() / 1)).zfill(2)}:{str(int(model.evaluate(end_time_var[0]).as_real().as_long() % 1 * 60)).zfill(2)}"

print(solution)