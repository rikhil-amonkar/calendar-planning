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
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
s.add(0 <= start_hour)
s.add(start_hour <= 12)
s.add(0 <= start_minute)
s.add(start_minute <= 30)
s.add(0 <= end_hour)
s.add(end_hour <= 12)
s.add(0 <= end_minute)
s.add(end_minute <= 30)

# Add constraints for each person
for i in kimberly:
    s.add(Or((start_hour * 60 + start_minute + meeting_duration) > i, (end_hour * 60 + end_minute) <= i))
for i in marie:
    s.add(Or((start_hour * 60 + start_minute + meeting_duration) > i, (end_hour * 60 + end_minute) <= i))
for i in diana:
    s.add(Or((start_hour * 60 + start_minute + meeting_duration) > i, (end_hour * 60 + end_minute) <= i))

# Add Megan's preference
s.add(start_hour >= 10)

# Ensure the start time is on the hour
s.add(start_minute == 0)

# Ensure the end time is on the half hour
s.add(end_minute == 30)

# Solve the constraints
if s.check() == sat:
    model = s.model()
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {model[start_hour].as_long():02d}:00')
    print(f'End Time: {model[end_hour].as_long():02d}:30')
else:
    print('No solution found')