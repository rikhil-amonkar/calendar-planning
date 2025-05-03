from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Ann's busy schedule (times in minutes from midnight):
# Monday:
#   10:00-11:00 -> (600, 660)
#   13:30-14:00 -> (810, 840)
# Tuesday:
#   10:00-10:30 -> (600, 630)
#   11:30-12:00 -> (690, 720)
#   13:00-13:30 -> (780, 810)
#   15:00-16:00 -> (900, 960)
# Wednesday:
#   11:00-11:30 -> (660, 690)
#   12:30-14:00 -> (750, 840)
#   15:00-15:30 -> (900, 930)
#   16:30-17:00 -> (990, 1020)
# Thursday:
#   9:00-9:30   -> (540, 570)
#   10:00-10:30 -> (600, 630)
#   11:00-12:30 -> (660, 750)
#   15:00-16:00 -> (900, 960)
#   16:30-17:00 -> (990, 1020)
ann_busy = {
    0: [(600, 660), (810, 840)],
    1: [(600, 630), (690, 720), (780, 810), (900, 960)],
    2: [(660, 690), (750, 840), (900, 930), (990, 1020)],
    3: [(540, 570), (600, 630), (660, 750), (900, 960), (990, 1020)]
}

# Jeremy's busy schedule:
# Monday: 9:00-17:00 (entire day busy) -> (540,1020)
# Tuesday:
#   9:00-10:00 -> (540,600)
#   10:30-17:00 -> (630,1020)
# Wednesday: 9:00-17:00 (entire day busy) -> (540,1020)
# Thursday:
#   9:00-12:00   -> (540,720)
#   12:30-13:00  -> (750,780)
#   13:30-15:30  -> (810,930)
#   16:00-17:00  -> (960,1020)
jeremy_busy = {
    0: [(540, 1020)],
    1: [(540, 600), (630, 1020)],
    2: [(540, 1020)],
    3: [(540, 720), (750, 780), (810, 930), (960, 1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function to enforce that a meeting (starting at start_var, lasting 'duration' minutes)
# does not overlap with a busy interval (busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate over candidate days in order (Monday, Tuesday, Wednesday, Thursday)
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Ann's busy intervals constraints for the day.
    for (busy_start, busy_end) in ann_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add Jeremy's busy intervals constraints for the day.
    for (busy_start, busy_end) in jeremy_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Try possible start times minute-by-minute in the work hours.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
          day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")