from z3 import *

# Define the time slots for each person
time_slots = {
    'Christine': [(9, 30), (10, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 30), (15, 0), (16, 0), (16, 30)],
    'Janice': [(0, 0), (17, 0)],  # 0-17 for 24-hour format
    'Bobby': [(12, 0), (12, 30), (14, 30), (15, 0)],
    'Elizabeth': [(9, 0), (9, 30), (11, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (17, 0)],
    'Tyler': [(9, 0), (9, 30), (10, 0), (11, 0), (12, 0), (12, 30), (13, 0), (13, 30), (15, 30), (16, 0), (16, 30), (17, 0)],
    'Edward': [(9, 0), (9, 30), (10, 0), (11, 0), (11, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (17, 0)],
}

# Define the meeting duration
meeting_duration = 30

# Define the day to meet
day = 'Monday'

# Define the solver
solver = Solver()

# Define the start time variable
start_time = Int('start_time')

# Define the end time variable
end_time = Int('end_time')

# Add constraints for each person
for person, time_slots in time_slots.items():
    for time_slot in time_slots:
        if person!= 'Janice' or time_slot[0] < 13:
            solver.add(start_time + meeting_duration > time_slot[0])
            solver.add(start_time + meeting_duration > time_slot[1])
            solver.add(end_time < time_slot[1])

# Add constraints for Janice's preference
solver.add(start_time + meeting_duration > 13)

# Add constraints for the day and time range
solver.add(start_time >= 9)
solver.add(end_time <= 17)
solver.add(start_time + meeting_duration <= 17)

# Add constraints to ensure the start time is a multiple of 30 minutes
# Add constraints to ensure the end time is a multiple of 30 minutes
solver.add(start_time % 30 == 0)
solver.add(end_time % 30 == 0)

# Check if a solution exists
if solver.check() == sat:
    model = solver.model()
    start_time_val = model[start_time].as_long()
    end_time_val = model[end_time].as_long()
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {start_time_val:02d}:00')
    print(f'End Time: {end_time_val:02d}:00')
else:
    print('No solution exists')