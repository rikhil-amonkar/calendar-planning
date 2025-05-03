from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define the meeting start time variable (in minutes from midnight)
start = Int("start")

# Candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Nancy's busy schedule (in minutes)
# Monday:
#   10:00-10:30 -> (600, 630)
#   11:30-12:30 -> (690, 750)
#   13:30-14:00 -> (810, 840)
#   14:30-15:30 -> (870, 930)
#   16:00-17:00 -> (960, 1020)
# Tuesday:
#   9:30-10:30 -> (570, 630)
#   11:00-11:30 -> (660, 690)
#   12:00-12:30 -> (720, 750)
#   13:00-13:30 -> (780, 810)
#   15:30-16:00 -> (930, 960)
# Wednesday:
#   10:00-11:30 -> (600, 690)
#   13:30-16:00 -> (810, 960)
nancy_busy = {
    0: [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],
    1: [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],
    2: [(600, 690), (810, 960)]
}

# Jose's busy schedule (in minutes)
# Monday: 9:00-17:00 -> (540, 1020)
# Tuesday: 9:00-17:00 -> (540, 1020)
# Wednesday:
#   9:00-9:30 -> (540, 570)
#   10:00-12:30 -> (600, 750)
#   13:30-14:30 -> (810, 870)
#   15:00-17:00 -> (900, 1020)
jose_busy = {
    0: [(540, 1020)],
    1: [(540, 1020)],
    2: [(540, 570), (600, 750), (810, 870), (900, 1020)]
}

# Helper function to enforce that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order (Monday, then Tuesday, then Wednesday)
for day in candidate_days:
    solver = Solver()
    # Constrain the meeting time to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Nancy's busy constraints for the candidate day.
    for (busy_start, busy_end) in nancy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Jose's busy constraints for the candidate day.
    for (busy_start, busy_end) in jose_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try every minute of the day; choose the earliest available start time.
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
    # Convert from minutes to HH:MM.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".
          format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")