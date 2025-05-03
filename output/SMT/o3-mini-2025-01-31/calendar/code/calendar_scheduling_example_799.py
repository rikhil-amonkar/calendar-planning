from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define the meeting start time variable (in minutes from midnight)
start = Int("start")

# Candidate days: we represent Monday as 0, Tuesday as 1, and Wednesday as 2.
# Since Albert cannot meet on Tuesday, we only consider Monday and Wednesday.
candidate_days = [0, 2]

# Albert's busy schedule (in minutes)
# Tuesday:
#   9:00 to 9:30 -> (540, 570)
#   12:30 to 13:00 -> (750, 780)
# Wednesday:
#   14:00 to 15:00 -> (840, 900)
albert_busy = {
    1: [(540, 570), (750, 780)],
    2: [(840, 900)]
}
# Note: Albert has no meetings on Monday, so no intervals are needed for day 0.

# Marie's busy schedule (in minutes)
# Monday:
#   9:30 to 17:00 -> (570, 1020)
# Tuesday:
#   9:00 to 10:00 -> (540, 600)
#   10:30 to 17:00 -> (630, 1020)
# Wednesday:
#   9:00 to 17:00 -> (540, 1020)
marie_busy = {
    0: [(570, 1020)],
    1: [(540, 600), (630, 1020)],
    2: [(540, 1020)]
}

# Helper function that creates a constraint ensuring that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# We'll search over candidate days in order (Monday then Wednesday) for the earliest availability.
for day in candidate_days:
    solver = Solver()
    # Constrain meeting time to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Albert's busy constraints for the candidate day, if any.
    for (busy_start, busy_end) in albert_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Marie's busy constraints for the candidate day.
    for (busy_start, busy_end) in marie_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))

    # Search for the earliest valid starting minute on the day.
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
    # Convert minutes into HH:MM format.
    start_hr, start_minute = divmod(selected_start, 60)
    end_hr, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_minute, end_hr, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")