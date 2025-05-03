from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Given the preferences:
#   - Abigail would rather not meet on Monday, so Monday is disallowed.
#   - Albert cannot meet on Tuesday, so Tuesday is disallowed.
# Thus, we only consider Wednesday (day = 2).
candidate_days = [0, 1, 2]

# Abigail's busy schedule in minutes from midnight:
# Monday:    9:00-10:00 -> (540,600), 11:00-12:00 -> (660,720), 12:30-13:00 -> (750,780), 14:30-15:00 -> (870,900)
# Tuesday:   12:30-13:00 -> (750,780)
# Wednesday: 14:00-14:30 -> (840,870)
abigail_busy = {
    0: [(540, 600), (660, 720), (750, 780), (870, 900)],
    1: [(750, 780)],
    2: [(840, 870)]
}

# Albert's busy schedule in minutes from midnight:
# Monday:    9:00-9:30 -> (540,570), 10:00-11:00 -> (600,660), 12:00-14:30 -> (720,870), 15:00-15:30 -> (900,930), 16:30-17:00 -> (990,1020)
# Tuesday:   10:30-12:00 -> (630,720), 12:30-13:00 -> (750,780), 14:00-15:00 -> (840,900), 16:30-17:00 -> (990,1020)
# Wednesday: 9:30-10:30 -> (570,630), 12:00-13:30 -> (720,810), 14:30-15:30 -> (870,930)
albert_busy = {
    0: [(540,570), (600,660), (720,870), (900,930), (990,1020)],
    1: [(630,720), (750,780), (840,900), (990,1020)],
    2: [(570,630), (720,810), (870,930)]
}

# Helper: The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day when meeting is scheduled (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes from midnight

# Check candidate days in order (Monday, Tuesday, Wednesday)
# However, we will enforce the participants' day constraints.
for day in candidate_days:
    solver = Solver()
    
    # Ensure the meeting is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Enforce day-specific preferences/constraints:
    if day == 0:
        # Abigail would rather not meet on Monday.
        solver.add(False)  # Disallow Monday.
    elif day == 1:
        # Albert cannot meet on Tuesday.
        solver.add(False)  # Disallow Tuesday.
    # For Wednesday (day == 2), no extra day constraint.
    
    # Add Abigail's busy constraints for the day.
    for busy_start, busy_end in abigail_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Albert's busy constraints for the day.
    for busy_start, busy_end in albert_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Look for the earliest time slot minute-by-minute.
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
    # Convert meeting time from minutes to HH:MM.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")