from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Meeting start variable in minutes after midnight.
start = Int("start")

# Work hours (9:00 to 17:00) in minutes.
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Grace's busy schedule:
# Tuesday: 13:00 to 13:30 -> (780, 810)
# Wednesday: 14:30 to 15:00 -> (870, 900)
grace_busy = {
    1: [(780, 810)],
    2: [(870, 900)]
}

# Debra's busy schedule:
# Monday:
#   9:00 to 10:00  -> (540, 600)
#   11:30 to 12:00 -> (690, 720)
#   15:00 to 16:00 -> (900, 960)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   9:00 to 11:00  -> (540, 660)
#   11:30 to 14:00 -> (690, 840)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 17:00 -> (930, 1020)
# Wednesday:
#   10:00 to 15:00 -> (600, 900)
#   15:30 to 17:00 -> (930, 1020)
debra_busy = {
    0: [(540, 600), (690, 720), (900, 960), (990, 1020)],
    1: [(540, 660), (690, 840), (870, 900), (930, 1020)],
    2: [(600, 900), (930, 1020)]
}

# A helper function that asserts that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None
meeting_start_val = None

# Iterate over candidate days in order for the earliest possible option.
for day in candidate_days:
    solver = Solver()
    # The meeting must lie completely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Grace's busy schedule constraints for this day.
    for b in grace_busy.get(day, []):
        busy_start, busy_end = b
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Debra's busy schedule constraints for this day.
    for b in debra_busy.get(day, []):
        busy_start, busy_end = b
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search minute-by-minute for the earliest valid meeting time on this day.
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
    start_hr, start_min = divmod(meeting_start_val, 60)
    end_hr, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")