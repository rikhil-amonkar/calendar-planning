from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday']

# Define the hours of the day
hours = [9, 10, 11, 12, 13, 14, 15, 16, 17]

# Define the meeting duration in hours
meeting_duration = 0.5

# Define the constraints for Jesse's schedule
jesse_schedule = [
    (13, 14, 'Monday'),
    (14, 15, 'Monday'),
    (9, 9.5, 'Tuesday'),
    (13, 13.5, 'Tuesday'),
    (14, 15, 'Tuesday')
]

# Define the constraints for Lawrence's schedule
lawrence_schedule = [
    (9, 17, 'Monday'),
    (9.5, 10.5, 'Tuesday'),
    (11.5, 12.5, 'Tuesday'),
    (13, 13.5, 'Tuesday'),
    (14.5, 15.5, 'Tuesday'),
    (15.5, 16.5, 'Tuesday')
]

# Define the solver
s = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(2)]
start_time = [Real(f'start_time_{i}') for i in range(2)]
end_time = [start_time[i] + meeting_duration for i in range(2)]

# Define the constraints
for i in range(2):
    s.add(day[i] == False)  # Initialize day to False

for i in range(2):
    s.add(Implies(day[i], And(9 <= start_time[i], start_time[i] < 17)))  # Ensure start time is within work hours

for i in range(2):
    s.add(Implies(day[i], And(9 <= end_time[i], end_time[i] < 17)))  # Ensure end time is within work hours

for i in range(2):
    for j in jesse_schedule:
        if j[2] == days[i]:
            s.add(Implies(day[i], And(start_time[i] > j[1], end_time[i] < j[0])))  # Ensure meeting time does not conflict with Jesse's schedule

for i in range(2):
    for j in lawrence_schedule:
        if j[2] == days[i]:
            s.add(Implies(day[i], And(start_time[i] > j[1], end_time[i] < j[0])))  # Ensure meeting time does not conflict with Lawrence's schedule

    # Ensure meeting time does not conflict with Lawrence's schedule after 16:30 on Tuesday
    s.add(Implies(day[1], start_time[1] > 16.5))

# Find a solution
s.add(Or([day[0], day[1]]))  # Ensure at least one day is True
s.add(day[1])  # Ensure Tuesday is chosen

if s.check() == sat:
    model = s.model()
    day_value = [int(model.evaluate(day[i]).as_bool()) for i in range(2)]
    start_time_value = [model.evaluate(start_time[i]).as_real().as_decimal('2.2').value() for i in range(2)]
    end_time_value = [model.evaluate(end_time[i]).as_real().as_decimal('2.2').value() for i in range(2)]

    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {days[day_value.index(1)]}")
    print(f"Start Time: {int(start_time_value[day_value.index(1)])}:{int((start_time_value[day_value.index(1)] - int(start_time_value[day_value.index(1)])) * 60):02d}")
    print(f"End Time: {int(end_time_value[day_value.index(1)])}:{int((end_time_value[day_value.index(1)] - int(end_time_value[day_value.index(1)])) * 60):02d}")
else:
    print("No solution found.")