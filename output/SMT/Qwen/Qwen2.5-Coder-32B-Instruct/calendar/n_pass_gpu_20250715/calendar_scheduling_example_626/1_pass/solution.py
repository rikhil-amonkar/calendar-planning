from z3 import *

# Define variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define constants for time slots
meeting_duration = 60  # 1 hour in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Create a solver instance
solver = Solver()

# Add constraints for valid day
solver.add(Or(day == 0, day == 1))

# Add constraints for valid start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Patricia's schedule constraints
# Monday: 10:00-10:30, 11:30-12:00, 13:00-13:30, 14:30-15:30, 16:00-16:30
solver.add(Or(start_time + meeting_duration <= 10 * 60, start_time >= 10 * 60 + 30))
solver.add(Or(start_time + meeting_duration <= 11 * 60 + 30, start_time >= 12 * 60))
solver.add(Or(start_time + meeting_duration <= 13 * 60, start_time >= 13 * 60 + 30))
solver.add(Or(start_time + meeting_duration <= 14 * 60 + 30, start_time >= 15 * 60))
solver.add(Or(start_time + meeting_duration <= 16 * 60, start_time >= 16 * 60 + 30))

# Tuesday: 10:00-10:30, 11:00-12:00, 14:00-16:00, 16:30-17:00
solver.add(Or(start_time + meeting_duration <= 10 * 60 + 30, start_time >= 10 * 60 + 30, day != 0))
solver.add(Or(start_time + meeting_duration <= 11 * 60, start_time >= 12 * 60, day != 0))
solver.add(Or(start_time + meeting_duration <= 14 * 60, start_time >= 16 * 60, day != 0))
solver.add(Or(start_time + meeting_duration <= 16 * 60 + 30, start_time >= 17 * 60, day != 0))

# Jesse's schedule constraints
# Monday: 9:00-17:00 (blocked all day)
solver.add(day != 0)  # Jesse is not available on Monday

# Tuesday: 11:00-11:30, 12:00-12:30, 13:00-14:00, 14:30-15:00, 15:30-17:00
solver.add(Or(start_time + meeting_duration <= 11 * 60, start_time >= 11 * 60 + 30, day != 1))
solver.add(Or(start_time + meeting_duration <= 12 * 60, start_time >= 12 * 60 + 30, day != 1))
solver.add(Or(start_time + meeting_duration <= 13 * 60, start_time >= 14 * 60, day != 1))
solver.add(Or(start_time + meeting_duration <= 14 * 60 + 30, start_time >= 15 * 60, day != 1))
solver.add(Or(start_time + meeting_duration <= 15 * 60 + 30, start_time >= 17 * 60, day != 1))

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time // 60:02}:{meeting_start_time % 60:02}")
    print(f"End Time: {meeting_end_time // 60:02}:{meeting_end_time % 60:02}")
else:
    print("No solution found")