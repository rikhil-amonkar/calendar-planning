from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes (1 hour)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define Z3 integer variable for meeting start time (in minutes from midnight)
start = Int("start")

# Candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Michelle's busy schedule (times in minutes)
# Monday:
#   9:30 - 10:00 -> (570, 600)
#   11:30 - 12:00 -> (690, 720)
#   13:00 - 14:00 -> (780, 840)
#   14:30 - 15:00 -> (870, 900)
# Tuesday:
#   11:00 - 11:30 -> (660, 690)
#   12:00 - 13:00 -> (720, 780)
#   13:30 - 14:00 -> (810, 840)
#   15:00 - 15:30 -> (900, 930)
#   16:00 - 17:00 -> (960, 1020)
# Wednesday:
#   13:00 - 14:00 -> (780, 840)
#   14:30 - 15:00 -> (870, 900)
#   15:30 - 16:00 -> (930, 960)
michelle_busy = {
    0: [(570, 600), (690, 720), (780, 840), (870, 900)],
    1: [(660, 690), (720, 780), (810, 840), (900, 930), (960, 1020)],
    2: [(780, 840), (870, 900), (930, 960)]
}

# Joshua's busy schedule (times in minutes)
# Monday:
#   9:00 - 13:00 -> (540, 780)
#   13:30 - 17:00 -> (810, 1020)
# Tuesday:
#   9:00 - 12:30 -> (540, 750)
#   13:00 - 15:30 -> (780, 930)
#   16:00 - 17:00 -> (960, 1020)
# Wednesday:
#   9:00 - 10:30 -> (540, 630)
#   11:30 - 13:30 -> (690, 810)
#   14:30 - 16:30 -> (870, 990)
joshua_busy = {
    0: [(540, 780), (810, 1020)],
    1: [(540, 750), (780, 930), (960, 1020)],
    2: [(540, 630), (690, 810), (870, 990)]
}

# Helper function: meeting interval [start, start+duration) must not overlap with busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order (Monday, then Tuesday, then Wednesday) to find the earliest availability
for day in candidate_days:
    solver = Solver()
    # Constrain the meeting time to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Michelle's busy constraints for the candidate day.
    for (busy_start, busy_end) in michelle_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Joshua's busy constraints for the candidate day.
    for (busy_start, busy_end) in joshua_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try every minute from the start of the day to find the earliest possible meeting time.
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
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")