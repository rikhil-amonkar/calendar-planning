from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Based on constraints:
# - Debra does not want to meet on Wednesday.
# - Keith is busy all day Monday.
# Thus the only allowed day is Tuesday (day 1).
allowed_days = [1]

# Busy schedules (times in minutes from midnight)
# Debra's busy schedule:
debra_busy = {
    1: [ (10 * 60 + 30, 11 * 60),  # Tuesday: 10:30 to 11:00 -> (630,660)
         (13 * 60, 13 * 60 + 30) ]  # Tuesday: 13:00 to 13:30 -> (780,810)
}

# Keith's busy schedule:
keith_busy = {
    0: [ (9 * 60, 17 * 60) ],          # Monday: 9:00 to 17:00 -> (540,1020)
    1: [ (9 * 60, 11 * 60 + 30),         # Tuesday: 9:00 to 11:30 -> (540,690)
         (12 * 60, 13 * 60),             # Tuesday: 12:00 to 13:00 -> (720,780)
         (13 * 60 + 30, 17 * 60) ],       # Tuesday: 13:30 to 17:00 -> (810,1020)
    2: [ (9 * 60, 9 * 60 + 30),           # Wednesday: 9:00 to 9:30 -> (540,570)
         (10 * 60, 13 * 60),             # Wednesday: 10:00 to 13:00 -> (600,780)
         (13 * 60 + 30, 14 * 60),        # Wednesday: 13:30 to 14:00 -> (810,840)
         (14 * 60 + 30, 16 * 60),        # Wednesday: 14:30 to 16:00 -> (870,960)
         (16 * 60 + 30, 17 * 60) ]        # Wednesday: 16:30 to 17:00 -> (990,1020)
}

# Helper function: meeting [start, start+duration) must not overlap with busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # Will hold the day code for the meeting
meeting_start_val = None  # meeting start time in minutes from midnight

# We try each allowed day (in this case, only Tuesday is allowed).
for day in allowed_days:
    solver = Solver()
    # The meeting must completely occur during work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)

    # Add constraints from Debra's busy schedule on that day.
    for (busy_start, busy_end) in debra_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add constraints from Keith's busy schedule on that day.
    for (busy_start, busy_end) in keith_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Look for the earliest valid start time by checking minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    # Convert minutes into HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")