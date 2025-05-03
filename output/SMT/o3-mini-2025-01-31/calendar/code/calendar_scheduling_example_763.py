from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Meeting start variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 to 17:00 (in minutes after midnight)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Danielle has no meetings, so no busy schedule for her.
# Scott's busy schedule (in minutes):
# Monday:
#   9:30 to 10:00 -> (570, 600)
#   10:30 to 11:00 -> (630, 660)
#   11:30 to 13:00 -> (690, 780)
#   13:30 to 15:30 -> (810, 930)
#   16:00 to 17:00 -> (960, 1020)
# Tuesday:
#   9:00 to 9:30 -> (540, 570)
#   10:00 to 11:00 -> (600, 660)
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 15:30 -> (870, 930)
#   16:00 to 17:00 -> (960, 1020)
# Wednesday:
#   9:00 to 10:00 -> (540, 600)
#   12:00 to 12:30 -> (720, 750)
#   14:00 to 14:30 -> (840, 870)
#   15:00 to 16:00 -> (900, 960)
#   16:30 to 17:00 -> (990, 1020)
scott_busy = {
    0: [(570, 600), (630, 660), (690, 780), (810, 930), (960, 1020)],
    1: [(540, 570), (600, 660), (690, 750), (780, 810), (870, 930), (960, 1020)],
    2: [(540, 600), (720, 750), (840, 870), (900, 960), (990, 1020)]
}

# Helper function to ensure that the meeting interval [start, start+duration)
# DOES NOT overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None          # Day index for the meeting
meeting_start_val = None    # Meeting start time in minutes after midnight

# Iterate through candidate days in order (Monday, then Tuesday, then Wednesday)
for day in candidate_days:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Scott's busy constraints for the given day.
    for busy_start, busy_end in scott_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Danielle has no meetings.
    
    # Try each possible minute from WORK_START to WORK_END - duration
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