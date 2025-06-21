from z3 import *

# Define the day of the week (Monday = 0, Tuesday = 1,..., Sunday = 6)
day_of_week = [0]

# Define the start and end times (9:00 = 9, 17:00 = 17)
start_time = [9]
end_time = [17]

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Define the existing schedules for each participant
schedules = {
    'Walter': [],
    'Cynthia': [(9, 9.5), (10, 10.5), (13.5, 14.5), (15, 16)],
    'Ann': [(10, 11), (13, 13.5), (14, 15), (16, 16.5)],
    'Catherine': [(9, 11.5), (12.5, 13.5), (14.5, 17)],
    'Kyle': [(9, 9.5), (10, 11.5), (12, 12.5), (13, 14.5), (15, 16)]
}

# Define the solver
s = Solver()

# Define the variables
day = Int('day')
start = Real('start')
end = Real('end')

# Add the constraints
s.add(day == 0)  # Monday
s.add(start >= 9)  # Start time must be at least 9:00
s.add(end <= 17)  # End time must be at most 17:00
s.add(end - start >= meeting_duration)  # Meeting duration must be at least 30 minutes

# Check if the meeting time conflicts with anyone's schedule
for participant, schedule in schedules.items():
    for start_time_slot, end_time_slot in schedule:
        s.add(Or(start + meeting_duration < start_time_slot, end < start_time_slot))

# Check if the meeting time is within the work hours
s.add(And(start >= 9, end <= 17))

# Check if the meeting time is a multiple of 30 minutes
s.add(start == IntVal(int(start)))
s.add(end == IntVal(int(end)))
s.add((end - start) % 30 == 0)

# Solve the constraints
if s.check() == sat:
    model = s.model()
    print('SOLUTION:')
    print(f'Day: {model[day]}')
    print(f'Start Time: {model[start]:.2f}')
    print(f'End Time: {model[end]:.2f}')
else:
    print('No solution found.')