from z3 import *

# Define the variables
day = 'Monday'
duration = 30  # in minutes

# Existing schedules for each participant
raymond_schedule = [
    (9, 30),
    (11, 30, 12),
    (13, 30),
    (15, 30)
]
billy_schedule = [
    (10, 30),
    (12, 13),
    (16, 30, 17)
]
donald_schedule = [
    (9, 30),
    (10, 11),
    (12, 13),
    (14, 14, 30),
    (16, 17)
]

# Billy's preference to avoid meetings after 15:00
billy_preference = (15, 0)

# Define the solver
s = Solver()

# Define the variables for the meeting time
start_time = Int('start_time')
end_time = start_time + duration

# Ensure the meeting is within work hours
s.add(9 <= start_time, end_time <= 17)

# Ensure the meeting does not conflict with anyone's schedule
for i in range(len(raymond_schedule)):
    if i % 2 == 0:  # start time
        s.add(Or(start_time >= raymond_schedule[i][0], start_time + duration <= raymond_schedule[i][0]))
    else:  # end time
        s.add(Or(end_time >= raymond_schedule[i][0], end_time <= raymond_schedule[i][0]))

for i in range(len(billy_schedule)):
    if i % 2 == 0:  # start time
        s.add(Or(start_time >= billy_schedule[i][0], start_time + duration <= billy_schedule[i][0]))
    else:  # end time
        s.add(Or(end_time >= billy_schedule[i][0], end_time <= billy_schedule[i][0]))

for i in range(len(donald_schedule)):
    if i % 2 == 0:  # start time
        s.add(Or(start_time >= donald_schedule[i][0], start_time + duration <= donald_schedule[i][0]))
    else:  # end time
        s.add(Or(end_time >= donald_schedule[i][0], end_time <= donald_schedule[i][0]))

# Ensure Billy does not have meetings after 15:00
s.add(Or(start_time >= billy_preference[0], end_time <= billy_preference[1]))

# Check if a solution exists
if s.check() == sat:
    # Get the solution
    model = s.model()
    start_time_value = model[start_time].as_long()
    end_time_value = model[end_time].as_long()
    
    # Print the solution
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {start_time_value:02d}:{(start_time_value % 60):02d}')
    print(f'End Time: {end_time_value:02d}:{(end_time_value % 60):02d}')
else:
    print('No solution exists')