from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes (1 hour)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define the meeting start time variable (in minutes from midnight)
start = Int("start")

# Candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Walter's busy schedule (in minutes from midnight):
# Walter is only busy on Tuesday and Wednesday.
# Tuesday:
#   9:30 to 11:00 -> (570, 660)
#   12:00 to 12:30 -> (720, 750)
#   14:00 to 14:30 -> (840, 870)
# Wednesday:
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 14:30 -> (840, 870)
#   15:00 to 15:30 -> (900, 930)
walter_busy = {
    1: [(570, 660), (720, 750), (840, 870)],
    2: [(690, 750), (780, 810), (840, 870), (900, 930)]
}

# Janice's busy schedule (in minutes from midnight):
# Monday:
#   9:00 to 10:30 -> (540, 630)
#   11:30 to 12:00 -> (690, 720)
#   12:30 to 14:00 -> (750, 840)
#   14:30 to 15:00 -> (870, 900)
#   16:00 to 17:00 -> (960, 1020)
# Tuesday:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 12:00 -> (660, 720)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 15:00 -> (810, 900)
#   15:30 to 16:30 -> (930, 990)
# Wednesday:
#   11:00 to 12:00 -> (660, 720)
#   13:30 to 14:30 -> (810, 870)
#   16:00 to 16:30 -> (960, 990)
janice_busy = {
    0: [(540, 630), (690, 720), (750, 840), (870, 900), (960, 1020)],
    1: [(600, 630), (660, 720), (750, 780), (810, 900), (930, 990)],
    2: [(660, 720), (810, 870), (960, 990)]
}

# A helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order (earlier days considered first)
for day in candidate_days:
    solver = Solver()
    
    # Ensure meeting is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Walter's busy interval constraints (if any for the day)
    for (busy_start, busy_end) in walter_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Janice's busy interval constraints
    for (busy_start, busy_end) in janice_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Look for the earliest possible start time in the work day.
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
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".
          format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")