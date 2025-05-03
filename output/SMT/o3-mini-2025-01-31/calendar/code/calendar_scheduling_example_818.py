from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Charles' busy schedule (in minutes from midnight):
# Monday: 16:30-17:00 -> (990, 1020)
# Tuesday: 9:00-9:30 -> (540, 570)
# Wednesday: 12:00-12:30 -> (720, 750); 14:00-14:30 -> (840, 870)
# Thursday: 10:30-11:00 -> (630, 660); 15:00-15:30 -> (900, 930)
charles_busy = {
    0: [(990, 1020)],
    1: [(540, 570)],
    2: [(720, 750), (840, 870)],
    3: [(630, 660), (900, 930)]
}

# Betty's busy schedule:
# Monday: 9:00-9:30 -> (540,570); 10:30-12:00 -> (630,720); 
#         12:30-13:00 -> (750,780); 14:00-15:00 -> (840,900); 15:30-17:00 -> (930,1020)
# Tuesday: 9:30-10:30 -> (570,630); 11:30-12:30 -> (690,750); 
#          13:30-14:00 -> (810,840); 14:30-15:30 -> (870,930)
# Wednesday: 9:00-9:30 -> (540,570); 10:00-11:30 -> (600,690); 
#            12:00-12:30 -> (720,750); 13:00-13:30 -> (780,810);
#            14:00-14:30 -> (840,870); 15:30-17:00 -> (930,1020)
# Thursday: 9:00-10:30 -> (540,630); 12:30-13:30 -> (750,810);
#           14:00-15:30 -> (840,930); 16:00-16:30 -> (960,990)
betty_busy = {
    0: [(540,570), (630,720), (750,780), (840,900), (930,1020)],
    1: [(570,630), (690,750), (810,840), (870,930)],
    2: [(540,570), (600,690), (720,750), (780,810), (840,870), (930,1020)],
    3: [(540,630), (750,810), (840,930), (960,990)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper: ensures that a meeting starting at 'start_var' for 'duration'
# minutes does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate over candidate days in order:
# Note the following preferences:
#   - Charles would rather not meet on Monday (day 0).
#   - Betty would like to avoid meetings on Tuesday after 13:30.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply preferences:
    # Charles's preference: skip Monday.
    if day == 0:
        solver.add(False)  # Disallow Monday
    
    # Betty's preference: if meeting on Tuesday (day 1), finish by 13:30.
    if day == 1:
        solver.add(start + duration <= 13 * 60 + 30)  # meeting must end by 13:30 (810 minutes)
    
    # Add Charles' busy constraints for the day.
    for (busy_start, busy_end) in charles_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add Betty's busy constraints for the day.
    for (busy_start, busy_end) in betty_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for the earliest possible start (minute-by-minute)
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
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")