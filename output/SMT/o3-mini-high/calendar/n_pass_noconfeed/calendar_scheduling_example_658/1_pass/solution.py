from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
# day: 0 = Monday, 1 = Tuesday
day = Int('day')
# start time in minutes (from midnight). Meeting duration is 30 minutes.
start = Int('start')
duration = 30

# The meeting must be scheduled on either Monday or Tuesday.
solver.add(Or(day == 0, day == 1))

# Meeting must be within working hours (9:00 to 17:00)
# 9:00 is 540 minutes and 17:00 is 1020 minutes.
solver.add(start >= 540)
solver.add(start + duration <= 1020)

# --------- Monday Schedules ---------
# Shirley's busy intervals on Monday: 10:30-11:00, 12:00-12:30, 16:00-16:30
mon_shirley_busy = [(630, 660), (720, 750), (960, 990)]
for bs, be in mon_shirley_busy:
    # If the meeting is on Monday, it must not overlap with the busy interval.
    solver.add(Or(day != 0, start + duration <= bs, start >= be))

# Albert is busy on Monday from 9:00 to 17:00.
solver.add(Or(day != 0, start + duration <= 540, start >= 1020))

# --------- Tuesday Schedules ---------
# Shirley's busy interval on Tuesday: 9:30-10:00 (570 to 600 minutes)
tue_shirley_busy = [(570, 600)]
for bs, be in tue_shirley_busy:
    solver.add(Or(day != 1, start + duration <= bs, start >= be))

# Albert's busy intervals on Tuesday:
# 9:30-11:00, 11:30-12:30, 13:00-16:00, 16:30-17:00 -> in minutes:
tue_albert_busy = [(570, 660), (690, 750), (780, 960), (990, 1020)]
for bs, be in tue_albert_busy:
    solver.add(Or(day != 1, start + duration <= bs, start >= be))

# Shirley’s preference: on Tuesday, she would rather not meet after 10:30 (i.e. the meeting must end by or before 10:30)
solver.add(Or(day != 1, start + duration <= 630))

# Check the constraints
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    meeting_day = model[day].as_long()

    # Helper function to convert minutes into HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = to_time_str(meeting_start)
    end_str = to_time_str(meeting_end)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"

    # Output in the requested format: Day and time range in HH:MM:HH:MM
    print(f"Meeting Day: {day_str}")
    print(f"Meeting Time: {start_str}:{end_str}")
else:
    print("No valid meeting time found.")