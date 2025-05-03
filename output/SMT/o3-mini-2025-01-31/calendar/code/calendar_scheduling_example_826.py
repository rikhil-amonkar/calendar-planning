from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540
WORK_END   = 17 * 60  # 1020

# Candidate days: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Cheryl's calendar is wide open (no busy intervals)
cheryl_busy = {
    0: [],
    1: [],
    2: [],
    3: []
}

# James's busy intervals (in minutes) by day:
# Monday:
#   9:00-9:30 -> (540,570)
#   10:30-11:00 -> (630,660)
#   12:30-13:00 -> (750,780)
#   14:30-15:30 -> (870,930)
#   16:30-17:00 -> (990,1020)
# Tuesday:
#   9:00-11:00 -> (540,660)
#   11:30-12:00 -> (690,720)
#   12:30-15:30 -> (750,930)
#   16:00-17:00 -> (960,1020)
# Wednesday:
#   10:00-11:00 -> (600,660)
#   12:00-13:00 -> (720,780)
#   13:30-16:00 -> (810,960)
# Thursday:
#   9:30-11:30 -> (570,690)
#   12:00-12:30 -> (720,750)
#   13:00-13:30 -> (780,810)
#   14:00-14:30 -> (840,870)
#   16:30-17:00 -> (990,1020)
james_busy = {
    0: [(540,570), (630,660), (750,780), (870,930), (990,1020)],
    1: [(540,660), (690,720), (750,930), (960,1020)],
    2: [(600,660), (720,780), (810,960)],
    3: [(570,690), (720,750), (780,810), (840,870), (990,1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function: Ensures that a meeting starting at start_var (lasting 'duration')
# does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Preference: Cheryl would rather not meet on Wednesday.
# Additionally, we want the meeting at the earliest availability.
# We'll iterate over candidate days in order (Monday, Tuesday, Wednesday, Thursday),
# and for each day iterate minute-by-minute from WORK_START to WORK_END - duration.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    # Constrain meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Enforce Cheryl's preference: avoid Wednesday.
    if day == 2:
        solver.add(False)
    
    # Add Cheryl's busy constraints (none in this case)
    for (busy_start, busy_end) in cheryl_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add James's busy intervals.
    for (busy_start, busy_end) in james_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
        
    # Check each minute possibility for the meeting start.
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
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")