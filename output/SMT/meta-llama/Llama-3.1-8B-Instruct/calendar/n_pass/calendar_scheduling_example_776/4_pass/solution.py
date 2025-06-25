from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday']

# Define the possible meeting times for each day
meeting_times = {
    'Monday': [(9, 11), (11, 13), (13, 14.5), (15, 17)],
    'Tuesday': [(9, 11.5), (12, 17)],
    'Wednesday': [(9, 11.5), (12, 12.5), (13, 14), (14.5, 16), (16.5, 17)]
}

# Define the constraints for Jennifer's schedule
jenkins_constraints = {
    'Monday': [(9, 11), (11.5, 13), (13.5, 14.5), (15, 17)],
    'Tuesday': [(9, 11.5), (12, 17)],
    'Wednesday': [(9, 11.5), (12, 12.5), (13, 14), (14.5, 16), (16.5, 17)]
}

# Define the constraints for John's schedule
john_constraints = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': []
}

# Define the meeting duration
meeting_duration = 0.5

# Define the solver
solver = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time = [Real(f'start_time_{i}') for i in range(len(days))]
end_time = [start_time[i] + Real(f'meeting_duration_{i}') for i in range(len(days))]

# Add the constraints
for i, d in enumerate(days):
    solver.add(day[i])
    solver.add(start_time[i] >= 9)
    solver.add(start_time[i] <= 17)
    solver.add(end_time[i] >= 9)
    solver.add(end_time[i] <= 17)
    for j, (s, e) in enumerate(meeting_times[d]):
        solver.add(Or(start_time[i] < s, start_time[i] > e))
        solver.add(Or(end_time[i] < s, end_time[i] > e))
    for j, (s, e) in enumerate(jenkins_constraints[d]):
        solver.add(Or(start_time[i] < s, start_time[i] > e))
        solver.add(Or(end_time[i] < s, end_time[i] > e))
    for j, (s, e) in enumerate(john_constraints[d]):
        solver.add(Or(start_time[i] < s, start_time[i] > e))
        solver.add(Or(end_time[i] < s, end_time[i] > e))

# Add the meeting duration constraint
for i in range(len(days)):
    solver.add(And(start_time[i] + Real('meeting_duration') >= 0.5, end_time[i] - start_time[i] == Real('meeting_duration')))

# Add the John's preference constraint
solver.add(Or(Not(day[0]), start_time[0] > 14.5))
solver.add(Or(Not(day[1]), start_time[1] > 9))
solver.add(Or(Not(day[2]), start_time[2] > 9))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_to_meet = days[int(model[day[0]].decl().name())]
    start_time_to_meet = str(int(model[start_time[0]].as_real().numerator / 60)) + ":" + str(int(model[start_time[0]].as_real().numerator % 60)).zfill(2)
    end_time_to_meet = str(int((model[end_time[0]].as_real().numerator + 30) / 60)) + ":" + str(int((model[end_time[0]].as_real().numerator + 30) % 60)).zfill(2)
    print(f"SOLUTION: Day: {day_to_meet}")
    print(f"Start Time: {start_time_to_meet} (24-hour format)")
    print(f"End Time: {end_time_to_meet} (24-hour format)")
else:
    print("No solution found")