from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday']

# Define the time slots for Susan and Sandra
susan_schedule = {
    'Monday': [(12, 30), (13, 30), (14, 30)],
    'Tuesday': [(11, 30), (12, 0)],
    'Wednesday': [(9, 30), (14, 0), (15, 30)]
}

sandra_schedule = {
    'Monday': [(9, 0), (14, 0), (16, 0), (16, 30)],
    'Tuesday': [(9, 0), (10, 30), (12, 30), (14, 0), (16, 0)],
    'Wednesday': [(9, 0), (12, 0), (13, 0), (17, 0)]
}

# Define the meeting duration
meeting_duration = 30

# Define the solver
solver = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time = [Int(f'start_time_{i}') for i in range(len(days))]
end_time = [Int(f'end_time_{i}') for i in range(len(days))]

# Define the constraints
for i in range(len(days)):
    solver.add(day[i])  # Initially, all days are possible

# Susan's constraints
for i in range(len(days)):
    for j in range(len(susan_schedule[days[i]])):
        start, end = susan_schedule[days[i]][j]
        solver.add(day[i] == False)  # Susan is not available at this time
        solver.add(start_time[i] >= start)
        solver.add(end_time[i] <= end)

# Sandra's constraints
for i in range(len(days)):
    for j in range(len(sandra_schedule[days[i]])):
        start, end = sandra_schedule[days[i]][j]
        solver.add(day[i] == False)  # Sandra is not available at this time
        solver.add(start_time[i] >= start)
        solver.add(end_time[i] <= end)

# Meeting duration constraint
for i in range(len(days)):
    solver.add(end_time[i] - start_time[i] == meeting_duration)

# Susan's preference constraint
solver.add(day[1] == False)  # Susan prefers not to meet on Tuesday

# Sandra's constraint
solver.add(Implies(day[0] == True, start_time[0] >= 16))  # Sandra can't meet on Monday after 16:00

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    # Print the solution
    for i in range(len(days)):
        if model.eval(day[i]):
            day_str = days[i]
            start_time_str = str(model.eval(start_time[i])).split('.')[0]
            end_time_str = str(model.eval(end_time[i])).split('.')[0]
            print(f'DAY: {day_str}')
            print(f'START TIME: {start_time_str}')
            print(f'END TIME: {end_time_str}')
            break
else:
    print("No solution exists")