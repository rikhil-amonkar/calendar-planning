from z3 import *

# Create a solver instance
solver = Solver()

# Define variables:
#   day: 0 for Monday, 1 for Tuesday
#   start: meeting start time in minutes from midnight
day = Int('day')
start = Int('start')
duration = 30
end = start + duration

# Meeting must occur within work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, end <= 1020)
# Ensure there's enough room for a 30-minute meeting: start can be at most 990 minutes.
solver.add(start <= 990)

# The meeting can only be on Monday (0) or Tuesday (1)
solver.add(Or(day == 0, day == 1))

# Doris prefers not to meet on Monday after 14:00.
# We'll interpret that as the meeting must finish by 14:00 (840 minutes) on Monday.
solver.add(Implies(day == 0, end <= 840))

# Jean's existing schedule:
# Jean is busy on Tuesday:
#   Busy from 11:30 to 12:00 -> minutes [690, 720]
#   Busy from 16:00 to 16:30 -> minutes [960, 990]
solver.add(Implies(day == 1, And(
    Or(end <= 690, start >= 720),
    Or(end <= 960, start >= 990)
)))

# Doris's existing schedule:
# On Monday, Doris has meetings at:
#   9:00 to 11:30 -> [540, 690]
#   12:00 to 12:30 -> [720, 750]
#   13:30 to 16:00 -> [810, 960]
#   16:30 to 17:00 -> [990, 1020]
monday_busy = And(
    Or(end <= 540, start >= 690),   # Avoid 9:00-11:30
    Or(end <= 720, start >= 750),    # Avoid 12:00-12:30
    Or(end <= 810, start >= 960),    # Avoid 13:30-16:00
    Or(end <= 990, start >= 1020)    # Avoid 16:30-17:00
)
solver.add(Implies(day == 0, monday_busy))

# On Tuesday, Doris is busy from 9:00 to 17:00 -> [540, 1020]
solver.add(Implies(day == 1, Or(end <= 540, start >= 1020)))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    scheduled_day = model[day].as_long()
    scheduled_start = model[start].as_long()
    scheduled_end = scheduled_start + duration

    # Convert minute counts to HH:MM (24-hour format)
    def format_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"

    day_str = "Monday" if scheduled_day == 0 else "Tuesday"
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {format_time(scheduled_start)}")
    print(f"End Time: {format_time(scheduled_end)}")
else:
    print("No solution found.")