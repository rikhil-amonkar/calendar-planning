from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# The meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours in minutes: from 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# According to the constraint, Jerry would like to avoid meetings on Monday and Wednesday,
# so we only consider Tuesday.
candidate_days = [1]

# Busy schedules in minutes

# Gary's busy schedule:
# Monday:   9:30 to 10:00 -> (570, 600),
#           12:00 to 12:30 -> (720, 750),
#           13:00 to 13:30 -> (780, 810),
#           14:30 to 15:00 -> (870, 900)
# Tuesday:  10:30 to 11:30 -> (630, 690),
#           12:30 to 13:00 -> (750, 780)
# Wednesday: 9:00 to 9:30  -> (540, 570),
#            12:30 to 13:30 -> (750, 810),
#            14:00 to 14:30 -> (840, 870),
#            15:00 to 15:30 -> (900, 930)
gary_busy = {
    0: [(570, 600), (720, 750), (780, 810), (870, 900)],
    1: [(630, 690), (750, 780)],
    2: [(540, 570), (750, 810), (840, 870), (900, 930)]
}

# Jerry's busy schedule:
# Monday:   9:00 to 11:00 -> (540, 660),
#           11:30 to 12:00 -> (690, 720),
#           14:00 to 15:30 -> (840, 930),
#           16:00 to 16:30 -> (960, 990)
# Tuesday:  9:00 to 10:00 -> (540, 600),
#           10:30 to 17:00 -> (630, 1020)
# Wednesday: 9:30 to 10:00  -> (570, 600),
#            10:30 to 11:00 -> (630, 660),
#            11:30 to 12:00 -> (690, 720),
#            12:30 to 13:00 -> (750, 780),
#            14:00 to 14:30 -> (840, 870),
#            15:00 to 16:00 -> (900, 960),
#            16:30 to 17:00 -> (990, 1020)
jerry_busy = {
    0: [(540, 660), (690, 720), (840, 930), (960, 990)],
    1: [(540, 600), (630, 1020)],
    2: [(570, 600), (630, 660), (690, 720), (750, 780), (840, 870), (900, 960), (990, 1020)]
}

# Helper function that asserts the meeting [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Search for a meeting time satisfying all constraints
found = False
meeting_day = None       # day index (0, 1, or 2)
meeting_start_val = None # meeting start time (in minutes after midnight)

# Check candidate days (only Tuesday in this case)
for day in candidate_days:
    solver = Solver()
    # Ensure the meeting is within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Gary's busy constraints for the day
    for busy_start, busy_end in gary_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Jerry's busy constraints for the day
    for busy_start, busy_end in jerry_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
        
    # Find the earliest valid meeting start time on this day
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()  # pop temporary constraint
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")