from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the work hours in minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Define the days
monday = 0
tuesday = 1
wednesday = 2

# Constraints for days
solver.add(day >= monday)
solver.add(day <= wednesday)

# Constraints for start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Martha's blocked times
martha_blocked_times = [
    (monday, 420, 480),  # 16:00 to 17:00
    (tuesday, 390, 420),  # 15:00 to 15:30
    (wednesday, 60, 120),  # 10:00 to 11:00
    (wednesday, 300, 330)  # 14:00 to 14:30
]

# Beverly's blocked times
beverly_blocked_times = [
    (monday, 0, 390),  # 9:00 to 13:30
    (monday, 420, 480),  # 14:00 to 17:00
    (tuesday, 0, 480),  # 9:00 to 17:00
    (wednesday, 54, 390),  # 9:30 to 15:30
    (wednesday, 420, 480)  # 16:30 to 17:00
]

# Add constraints for Martha's blocked times
for d, s, e in martha_blocked_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + meeting_duration <= s)))

# Add constraints for Beverly's blocked times
for d, s, e in beverly_blocked_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + meeting_duration <= s)))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert meeting start and end times to HH:MM format
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = 9 + meeting_end // 60
    end_minute = meeting_end % 60

    # Print the solution
    print("SOLUTION:")
    print(f"Day: {'Monday' if meeting_day == 0 else 'Tuesday' if meeting_day == 1 else 'Wednesday'}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")