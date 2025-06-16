from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday']

# Define the hours of the day
hours = range(9, 18)

# Define the meeting duration
meeting_duration = 0.5

# Define the existing schedules for Nicole and Ruth
nicole_schedule = {
    'Monday': [(9, 9.5), (13, 13.5), (14.5, 15.5)],
    'Tuesday': [(9, 9.5), (11.5, 13.5), (14.5, 15.5)],
    'Wednesday': [(10, 11), (12.5, 15), (16, 17)]
}

ruth_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9.5, 10.5), (11, 11.5), (12, 12.5), (13.5, 15.5), (16, 16.5)]
}

# Define Ruth's preference
ruth_preference = {
    'Wednesday': [(13.5, 17)]
}

# Define the solver
solver = Optimize()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time = [Real(f'start_time_{i}') for i in range(len(days))]
end_time = [Real(f'end_time_{i}') for i in range(len(days))]

# Define the constraints
for i in range(len(days)):
    solver.add(day[i] == False)  # Initialize day[i] to False

for i in range(len(days)):
    for j in range(len(hours)):
        for k in range(len(hours)):
            if k - j == int(meeting_duration * 2):
                # Check if the meeting time conflicts with Nicole's schedule
                if days[i] in nicole_schedule and (j, k) in nicole_schedule[days[i]]:
                    solver.add(day[i] == False)
                # Check if the meeting time conflicts with Ruth's schedule
                if days[i] in ruth_schedule and (j, k) in ruth_schedule[days[i]]:
                    solver.add(day[i] == False)
                # Check if the meeting time conflicts with Ruth's preference
                if days[i] in ruth_preference and (j, k) in ruth_preference[days[i]]:
                    solver.add(day[i] == False)
                # If the meeting time does not conflict with anyone's schedule, add it to the solver
                solver.add(day[i] == True)
                solver.add(start_time[i] == j)
                solver.add(end_time[i] == k)

# Solve the optimization problem
solution = solver.check()

if solution == sat:
    model = solver.model()
    day_idx = [model.evaluate(day[i]).as_bool() for i in range(len(days))].index(True)
    print(f'SOLUTION:')
    print(f'Day: {days[day_idx]}')
    print(f'Start Time: {model.evaluate(start_time[day_idx]).as_real().as_decimal().limit_denominator()}')
    print(f'End Time: {model.evaluate(end_time[day_idx]).as_real().as_decimal().limit_denominator()}')
else:
    print('No solution found')