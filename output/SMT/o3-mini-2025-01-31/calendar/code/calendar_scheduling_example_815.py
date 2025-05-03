from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes (1 hour)
duration = 60

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Sarah's calendar is wide open the entire week (no busy intervals).

# Timothy's busy schedule (times in minutes from midnight):
# Monday:
# 10:00-10:30 -> (600, 630)
# 11:30-12:00 -> (690, 720)
# 12:30-13:00 -> (750, 780)
# 13:30-15:30 -> (810, 930)
# 16:30-17:00 -> (990,1020)
# Tuesday:
# 10:00-10:30 -> (600, 630)
# 11:00-13:00 -> (660, 780)
# 14:00-14:30 -> (840, 870)
# 15:00-15:30 -> (900, 930)
# 16:00-16:30 -> (960, 990)
# Wednesday:
# 9:00-9:30   -> (540, 570)
# 10:00-10:30 -> (600, 630)
# 11:30-13:00 -> (690, 780)
# 13:30-14:00 -> (810, 840)
# 14:30-15:30 -> (870, 930)
# 16:00-16:30 -> (960, 990)
# Thursday:
# 9:00-10:00  -> (540, 600)
# 10:30-12:00 -> (630, 720)
# 13:00-13:30 -> (780, 810)
# 15:00-16:30 -> (900, 990)
timothy_busy = {
    0: [(600, 630), (690, 720), (750, 780), (810, 930), (990, 1020)],
    1: [(600, 630), (660, 780), (840, 870), (900, 930), (960, 990)],
    2: [(540, 570), (600, 630), (690, 780), (810, 840), (870, 930), (960, 990)],
    3: [(540, 600), (630, 720), (780, 810), (900, 990)]
}

# Timothy would rather not meet on Tuesday.
# We will enforce this by skipping day == 1 (Tuesday).

solution_found = False
selected_day = None
selected_start = None

# Helper function: ensure that a meeting starting at 'start_var' (lasting 'duration')
# does not overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate through candidate days in order (Monday, Tuesday, Wednesday, Thursday)
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Timothy's busy intervals constraints
    for (busy_start, busy_end) in timothy_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
        
    # Add preference constraint: Timothy would rather not have a meeting on Tuesday
    if day == 1:
        solver.add(False)  # Force unsat for Tuesday.
    
    # Search through possible start times minute-by-minute
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
    # Convert minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")