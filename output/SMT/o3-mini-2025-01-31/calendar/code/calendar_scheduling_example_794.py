from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Create a Z3 integer variable for the meeting start time (in minutes from midnight)
start = Int("start")

# Candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Denise is free all week, but she would rather not meet on Monday.
# Jesse's busy schedule (times in minutes from midnight):

# Monday:
#   11:30 to 13:00 -> (690, 780)
#   13:30 to 16:00 -> (810, 960)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   9:00 to 10:30 -> (540, 630)
#   11:30 to 12:00 -> (690, 720)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 16:30 -> (900, 990)
# Wednesday:
#   9:00 to 10:00 -> (540, 600)
#   10:30 to 13:30 -> (630, 810)
#   14:30 to 17:00 -> (870, 1020)
jesse_busy = {
    0: [(690, 780), (810, 960), (990, 1020)],
    1: [(540, 630), (690, 720), (810, 840), (900, 990)],
    2: [(540, 600), (630, 810), (870, 1020)]
}

# Preferences/constrains:
# Denise would rather not meet on Monday -> We treat this as a constraint: no meeting on Monday.
# Jesse cannot meet on Wednesday -> meeting on Wednesday is disallowed.
def preferences(day):
    constraints = []
    if day == 0:  # Monday
        constraints.append(False)  # Force unsat for Monday
    if day == 2:  # Wednesday
        constraints.append(False)  # Force unsat for Wednesday
    return constraints

# A helper function to ensure that the meeting interval [start, start + duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order (Monday, Tuesday, Wednesday)
for day in candidate_days:
    solver = Solver()
    
    # Constrain meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add preferences: for Denise (avoid Monday) and for Jesse (cannot meet on Wednesday).
    for pref in preferences(day):
        solver.add(pref)
    
    # Add Jesse's busy intervals constraints for the given day.
    for (busy_start, busy_end) in jesse_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate over each possible starting time in minutes (earliest availability search)
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
    # Convert minutes to HH:MM
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")