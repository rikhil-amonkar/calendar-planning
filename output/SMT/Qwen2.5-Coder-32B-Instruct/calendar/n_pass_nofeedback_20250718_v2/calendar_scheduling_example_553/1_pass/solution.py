from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (9 to 17 in 24-hour format)
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes

# Eric's blocked times
eric_blocked_times = [(12 * 60, 13 * 60), (14 * 60, 15 * 60)]

# Henry's blocked times
henry_blocked_times = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60),
                       (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
                       (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]

# Henry prefers not to meet after 10:00
henry_preference_end = 10 * 60

# Constraints for the meeting
solver.add(day == 1)  # Monday
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)
solver.add(end_time == start_time + meeting_duration)

# Eric's availability
for blocked_start, blocked_end in eric_blocked_times:
    solver.add(Or(start_time >= blocked_end, end_time <= blocked_start))

# Henry's availability
for blocked_start, blocked_end in henry_blocked_times:
    solver.add(Or(start_time >= blocked_end, end_time <= blocked_start))

# Henry's preference
solver.add(end_time <= henry_preference_end)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start_time].as_long()
    meeting_end = model[end_time].as_long()

    # Convert meeting start and end times from minutes to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60

    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")