from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define the meeting start time variable (in minutes from midnight)
start = Int("start")

# Map candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Thomas's busy schedule (in minutes) for each day:
# Monday: 9:00-10:30 -> (540,630), 11:00-14:00 -> (660,840), 14:30-16:30 -> (870,990)
# Tuesday: 11:00-11:30 -> (660,690), 14:00-14:30 -> (840,870), 16:00-16:30 -> (960,990)
# Wednesday: 9:30-10:00 -> (570,600), 12:00-12:30 -> (720,750), 14:00-15:00 -> (840,900)
thomas_busy = {
    0: [(540, 630), (660, 840), (870, 990)],
    1: [(660, 690), (840, 870), (960, 990)],
    2: [(570, 600), (720, 750), (840, 900)]
}

# Stephen's busy schedule (in minutes) for each day:
# Monday: 9:00-10:30 -> (540,630), 11:00-12:00 -> (660,720), 12:30-15:00 -> (750,900), 15:30-17:00 -> (930,1020)
# Tuesday: 9:00-9:30 -> (540,570), 10:00-10:30 -> (600,630), 11:00-11:30 -> (660,690), 12:00-17:00 -> (720,1020)
# Wednesday: 9:00-17:00 -> (540,1020)
stephen_busy = {
    0: [(540, 630), (660, 720), (750, 900), (930, 1020)],
    1: [(540, 570), (600, 630), (660, 690), (720, 1020)],
    2: [(540, 1020)]
}

# Thomas's preferences:
# - He does not want to meet on Monday (day 0).
# - On Tuesday (day 1), he does not want to meet before 11:00, so meeting start must be >= 660.
def thomas_preferences(day):
    constraints = []
    if day == 0:
        # Thomas doesn't want Monday -> unsat constraint
        constraints.append(False)
    if day == 1:
        # Tuesday: meeting should start at or after 11:00 (660 minutes)
        constraints.append(start >= 660)
    return constraints

# A helper function to assert that the meeting [start, start+duration) does not overlap a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days
for day in candidate_days:
    solver = Solver()
    
    # Add work hours constraint
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Thomas's personal preferences for this day.
    for pref in thomas_preferences(day):
        solver.add(pref)
    
    # Add Thomas's busy intervals constraints for given day.
    for (b_start, b_end) in thomas_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Stephen's busy intervals constraints for given day.
    for (b_start, b_end) in stephen_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try every possible starting minute within work hours.
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