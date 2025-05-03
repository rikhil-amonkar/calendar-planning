from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Given Doris is busy all day on Monday and Wednesday,
# and Doris cannot meet on Tuesday after 12:00, we only consider Tuesday.
candidate_days = [1]

# Bryan's busy schedule (in minutes):
# Monday: 13:00 to 13:30 -> (780, 810)
# Tuesday: (no busy times)
# Wednesday: 9:00 to 9:30 -> (540, 570), 11:30 to 12:00 -> (690, 720), 
#            16:00 to 16:30 -> (960, 990)
bryan_busy = {
    0: [(780, 810)],
    1: [],
    2: [(540, 570), (690, 720), (960, 990)]
}

# Doris's busy schedule (in minutes):
# Monday: busy all day 9:00 to 17:00 -> (540, 1020)
# Tuesday: 9:00 to 10:30 -> (540, 630), 11:00 to 16:00 -> (660, 960), 16:30 to 17:00 -> (990, 1020)
# Wednesday: busy all day 9:00 to 17:00 -> (540, 1020)
doris_busy = {
    0: [(540, 1020)],
    1: [(540, 630), (660, 960), (990, 1020)],
    2: [(540, 1020)]
}

# Helper function: ensures that the meeting [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day index (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

# We only consider Tuesday (day index = 1)
for day in candidate_days:
    solver = Solver()
    
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Tuesday, Doris cannot meet after 12:00.
    if day == 1:
        solver.add(start + duration <= 720)  # 12:00 is 720 minutes
    
    # Add Bryan's busy constraints for this day.
    for busy_start, busy_end in bryan_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Doris's busy constraints for this day.
    for busy_start, busy_end in doris_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Look for the earliest valid start time on this day.
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
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")