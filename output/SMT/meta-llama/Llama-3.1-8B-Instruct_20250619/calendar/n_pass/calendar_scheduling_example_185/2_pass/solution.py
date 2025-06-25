from z3 import *

# Define the day
day = 'Monday'

# Define the start and end times
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the existing schedules
kimberly = [10 * 60, 10 * 60 + 30, 11 * 60, 12 * 60, 16 * 60]
megan = []
marie = [10 * 60, 11 * 60, 11 * 60 + 30, 15 * 60, 16 * 60]
diana = [9 * 60 + 30, 10 * 60, 10 * 60 + 30, 14 * 60, 15 * 60 + 30]

# Define the preferences
megan_preference = 10 * 60  # Megan prefers to avoid meetings before 10:00

# Define the solver
s = Solver()

# Define the variables
start = Int('start')
end = Int('end')

# Define the constraints
s.add(0 <= start)
s.add(start + meeting_duration <= end)
s.add(end <= end_time)

# Add constraints for each person
for i in kimberly:
    s.add(Or(start + meeting_duration > i, end <= i))
for i in marie:
    s.add(Or(start + meeting_duration > i, end <= i))
for i in diana:
    s.add(Or(start + meeting_duration > i, end <= i))

# Add Megan's preference
s.add(start >= megan_preference)

# Ensure the start time is between 9:00 and 12:00
s.add(And(start >= 9 * 60, start <= 12 * 60))

# Ensure the end time is between 9:30 and 12:30
s.add(And(end >= 9 * 60 + 30, end <= 12 * 60 + 30))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {model[start] // 60:02d}:{model[start] % 60:02d}')
    print(f'End Time: {model[end] // 60:02d}:{model[end] % 60:02d}')
else:
    print('No solution found')