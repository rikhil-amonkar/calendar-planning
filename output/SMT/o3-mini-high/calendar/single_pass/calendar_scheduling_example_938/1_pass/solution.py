from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define integer variables:
# meeting_day: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
# meeting_start: start time in minutes from midnight.
meeting_day = Int('meeting_day')
meeting_start = Int('meeting_start')
meeting_duration = 30  # minutes

# Working hours: between 9:00 (540 minutes) and 17:00 (1020 minutes).
# The meeting must finish by 17:00 so meeting_start can be at most 1020-30 = 990.
solver.add(meeting_day >= 0, meeting_day <= 4)
solver.add(meeting_start >= 540, meeting_start <= 990)

# Eric prefers to avoid Wednesday.
solver.add(meeting_day != 2)

# Helper function to add busy-interval constraints.
# For a given day and busy interval [busy_start, busy_end],
# if the meeting is scheduled on that day then the meeting must not overlap the busy time.
def add_busy_constraint(day_val, busy_start, busy_end):
    # The meeting (from meeting_start to meeting_start+meeting_duration) must either end 
    # before the busy interval, or start after the busy interval.
    solver.add(Implies(meeting_day == day_val,
                       Or(meeting_start + meeting_duration <= busy_start,
                          meeting_start >= busy_end)))

# ======================
# Eugene's busy times:
# Monday (day == 0): 
#   11:00 to 12:00  -> [660, 720]
#   13:30 to 14:00  -> [810, 840]
#   14:30 to 15:00  -> [870, 900]
#   16:00 to 16:30  -> [960, 990]
if True:
    add_busy_constraint(0, 660, 720)
    add_busy_constraint(0, 810, 840)
    add_busy_constraint(0, 870, 900)
    add_busy_constraint(0, 960, 990)
    
# Tuesday (day == 1): No busy intervals for Eugene.

# Wednesday (day == 2):
#   9:00 to 9:30    -> [540, 570]
#   11:00 to 11:30  -> [660, 690]
#   12:00 to 12:30  -> [720, 750]
#   13:30 to 15:00  -> [810, 900]
if True:
    add_busy_constraint(2, 540, 570)
    add_busy_constraint(2, 660, 690)
    add_busy_constraint(2, 720, 750)
    add_busy_constraint(2, 810, 900)

# Thursday (day == 3):
#   9:30 to 10:00   -> [570, 600]
#   11:00 to 12:30  -> [660, 750]
if True:
    add_busy_constraint(3, 570, 600)
    add_busy_constraint(3, 660, 750)
    
# Friday (day == 4):
#   10:30 to 11:00  -> [630, 660]
#   12:00 to 12:30  -> [720, 750]
#   13:00 to 13:30  -> [780, 810]
if True:
    add_busy_constraint(4, 630, 660)
    add_busy_constraint(4, 720, 750)
    add_busy_constraint(4, 780, 810)

# ======================
# Eric's busy times:
# Monday (day == 0):
#   Busy entire day: 9:00 to 17:00 -> [540, 1020]
if True:
    add_busy_constraint(0, 540, 1020)

# Tuesday (day == 1):
#   Busy entire day: 9:00 to 17:00 -> [540, 1020]
if True:
    add_busy_constraint(1, 540, 1020)

# Wednesday (day == 2):
#   9:00 to 11:30   -> [540, 690]
#   12:00 to 14:00  -> [720, 840]
#   14:30 to 16:30  -> [870, 990]
if True:
    add_busy_constraint(2, 540, 690)
    add_busy_constraint(2, 720, 840)
    add_busy_constraint(2, 870, 990)

# Thursday (day == 3):
#   Busy entire day: 9:00 to 17:00 -> [540, 1020]
if True:
    add_busy_constraint(3, 540, 1020)

# Friday (day == 4):
#   9:00 to 11:00   -> [540, 660]
#   11:30 to 17:00  -> [690, 1020]
if True:
    add_busy_constraint(4, 540, 660)
    add_busy_constraint(4, 690, 1020)

# Check for a solution.
if solver.check() == sat:
    model = solver.model()
    selected_day = model[meeting_day].as_long()
    selected_start = model[meeting_start].as_long()
    selected_end = selected_start + meeting_duration

    # Map numeric day to day names.
    days_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    day_str = days_map[selected_day]

    # Convert minutes to HH:MM string.
    def format_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    start_time_str = format_time(selected_start)
    end_time_str = format_time(selected_end)

    # Print the solution as required.
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")