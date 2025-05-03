from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Judy would rather not meet on Monday so we only consider Tuesday and Wednesday.
allowed_days = [1, 2]

# Frank's busy schedule (in minutes from midnight)
# Tuesday: 9:30-10:00 -> (570,600), 16:30-17:00 -> (990,1020)
# Wednesday: 9:00-10:30 -> (540,630), 15:00-15:30 -> (900,930)
frank_busy = {
    1: [(570, 600), (990, 1020)],
    2: [(540, 630), (900, 930)]
}

# Judy's busy schedule (in minutes from midnight)
# Monday: 9:00-14:30 -> (540,870), 15:00-16:30 -> (900,990) [not to be used since Judy prefers not Monday]
# Tuesday: 10:00-10:30 -> (600,630), 11:30-13:00 -> (690,780), 14:00-14:30 -> (840,870),
#          15:00-15:30 -> (900,930), 16:30-17:00 -> (990,1020)
# Wednesday: 9:00-9:30 -> (540,570), 10:30-12:00 -> (630,720), 16:00-16:30 -> (960,990)
judy_busy = {
    1: [(600, 630), (690, 780), (840, 870), (900, 930), (990, 1020)],
    2: [(540, 570), (630, 720), (960, 990)]
}

# Helper function
# The meeting [start, start+duration) must not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day when meeting is scheduled (1=Tuesday, 2=Wednesday)
meeting_start_val = None # meeting start time in minutes from midnight

# Try each allowed day (in order: Tuesday, then Wednesday) and search minute-by-minute
for day in allowed_days:
    solver = Solver()
    
    # Ensure meeting is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Frank's busy constraint for the given day
    for b_start, b_end in frank_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Judy's busy constraint for the given day.
    for b_start, b_end in judy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate over possible starting times within work hours.
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
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")