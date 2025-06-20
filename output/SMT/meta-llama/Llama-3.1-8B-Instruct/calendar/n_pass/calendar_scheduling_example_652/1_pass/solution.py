from z3 import *

# Define the days of the week
MONDAY = 0
TUESDAY = 1

# Define the start and end times
START_TIME = 9
END_TIME = 17
MEETING_DURATION = 0.5  # in hours

# Define the existing schedules
jessie_schedule = [
    (MONDAY, 13.5, 14),
    (MONDAY, 14.5, 15),
    (TUESDAY, 9, 9.5),
    (TUESDAY, 13, 13.5),
    (TUESDAY, 14, 15)
]

lawrence_schedule = [
    (MONDAY, 9, 17),
    (TUESDAY, 9.5, 10),
    (TUESDAY, 11.5, 12),
    (TUESDAY, 13, 13.5),
    (TUESDAY, 14.5, 15),
    (TUESDAY, 15.5, 16.5)
]

# Define the constraints
def is_available(day, start_time, end_time, schedule):
    for d, s, e in schedule:
        if day == d and s < end_time and e > start_time:
            return False
    return True

# Define the solver
solver = Solver()

# Define the variables
day = Int('day')
start_time = Real('start_time')
end_time = Real('end_time')

# Add constraints
solver.add(day == MONDAY, Or(start_time >= 9, start_time <= 16.5))
solver.add(day == TUESDAY, Or(start_time >= 9, start_time <= 16.5))
solver.add(And(start_time + MEETING_DURATION <= end_time, end_time <= 17))
solver.add(is_available(day, start_time, end_time, jessie_schedule))
solver.add(is_available(day, start_time, end_time, lawrence_schedule))
solver.add(day!= TUESDAY or start_time > 16.5)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print('SOLUTION:')
    print(f'Day: {["Monday", "Tuesday"][model[day].as_long()]}')
    print(f'Start Time: {model[start_time].as_real().as_float():.2f}:00')
    print(f'End Time: {model[end_time].as_real().as_float():.2f}:00')
else:
    print('No solution found.')