YOUR_CODE
from z3 import *

# Define the day and time variables
day = [Bool('day_%d' % i) for i in range(1)]
time = [Bool('time_%d' % i) for i in range(96)]  # 96 intervals in a day (9:00 to 17:00, 30 minutes interval)

# Define the existing schedules for each participant
schedules = {
    'Joe': [(9*60 + 30, 10*60), (10*60, 11*60)],
    'Keith': [(11*60, 12*60), (15*60, 15*30)],
    'Patricia': [(9*60, 9*60 + 30), (13*60, 13*60 + 30)],
    'Nancy': [(9*60, 11*60), (11*60, 16*60)],
    'Pamela': [(9*60, 10*60), (10*60, 11*60), (11*60, 12*60), (13*60, 14*60), (14*60, 15*60), (15*60, 16*60), (16*60, 17*60)]
}

# Define the meeting duration
meeting_duration = 30

# Define the constraints
constraints = []
for i in range(96):
    constraints.append(Or([time[i]]))
    constraints.append(And([time[i]]))
    for participant, schedule in schedules.items():
        for start, end in schedule:
            if start <= i <= end:
                constraints.append(Not(time[i]))

# Define the objective function
objective = And([time[0]])

# Solve the problem
solver = Solver()
solver.add(constraints)
solver.add(day[0]) # Only one day of the week
for i in range(96):
    solver.add(Implies(day[0], time[i])) # Only one time of the day

if solver.check() == sat:
    model = solver.model()
    time_index = 0
    for i in range(96):
        if model.evaluate(time[i]):
            time_index = i
            break

    start_time = time_index // 2 * 30 + 9 * 60
    end_time = start_time + meeting_duration
    day_of_week = 1  # Monday
else:
    print("No solution found")

# Print the solution
if time_index!= 0:
    print("SOLUTION:")
    print(f"Day: {day_of_week}")
    print(f"Start Time: {start_time // 60:02d}:{start_time % 60:02d}")
    print(f"End Time: {end_time // 60:02d}:{end_time % 60:02d}")
else:
    print("No solution found")