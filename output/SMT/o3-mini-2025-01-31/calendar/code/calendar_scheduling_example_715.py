from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Since Jennifer cannot meet on Monday, we consider Tuesday and Wednesday.
allowed_days = [1, 2]

# Busy schedules: times are represented as tuples (start, end) in minutes since midnight.

# Jennifer's calendar is completely free, so no busy intervals.

# Denise's busy schedule:
denise_busy = {
    0: [ (9 * 60, 9 * 60 + 30),    # Monday: 9:00 to 9:30 -> (540,570)
         (10 * 60, 11 * 60),        # Monday: 10:00 to 11:00 -> (600,660)
         (11 * 60 + 30, 12 * 60),   # Monday: 11:30 to 12:00 -> (690,720)
         (13 * 60, 17 * 60) ],      # Monday: 13:00 to 17:00 -> (780,1020)
    1: [ (9 * 60 + 30, 10 * 60),   # Tuesday: 9:30 to 10:00 -> (570,600)
         (11 * 60, 11 * 60 + 30),   # Tuesday: 11:00 to 11:30 -> (660,690)
         (13 * 60 + 30, 14 * 60),   # Tuesday: 13:30 to 14:00 -> (810,840)
         (15 * 60, 16 * 60 + 30) ],  # Tuesday: 15:00 to 16:30 -> (900,990)
    2: [ (9 * 60 + 30, 11 * 60),    # Wednesday: 9:30 to 11:00 -> (570,660)
         (11 * 60 + 30, 12 * 60),   # Wednesday: 11:30 to 12:00 -> (690,720)
         (12 * 60 + 30, 13 * 60),   # Wednesday: 12:30 to 13:00 -> (750,780)
         (14 * 60 + 30, 15 * 60 + 30),  # Wednesday: 14:30 to 15:30 -> (870,930)
         (16 * 60, 16 * 60 + 30) ]   # Wednesday: 16:00 to 16:30 -> (960,990)
}

# Helper function to ensure the meeting [start, start+duration) does not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # Will hold the day code (1 for Tuesday, 2 for Wednesday)
meeting_start_val = None  # meeting start time as minutes from midnight

# We iterate through the allowed days in order.
# The group prefers the earliest availability, so we try Tuesday first (day 1), then Wednesday (day 2).
for day in allowed_days:
    solver = Solver()
    # Meeting must fit in work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Denise's busy schedule constraints for the given day.
    for (busy_start, busy_end) in denise_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Jennifer is free, so no additional constraints are needed for her.
    
    # Iterate minute-by-minute to find the earliest possible start time in the work window.
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
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")