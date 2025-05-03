from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedules in minutes (from midnight)

# Evelyn's busy schedule:
# Monday: 9:30-10:00, 12:00-12:30, 13:00-14:30
# Tuesday: 12:30-13:00, 13:30-14:00, 16:30-17:00
# Wednesday: 12:00-12:30, 16:30-17:00
# Thursday: 10:30-11:00, 11:30-12:00, 14:00-15:30, 16:30-17:00
evelyn_busy = {
    0: [(570, 600), (720, 750), (780, 870)],
    1: [(750, 780), (810, 840), (990, 1020)],
    2: [(720, 750), (990, 1020)],
    3: [(630, 660), (690, 720), (840, 930), (990, 1020)]
}

# Mark's busy schedule:
# Monday: 9:30-11:00, 11:30-12:30, 13:30-14:30, 15:30-16:00
# Tuesday: 9:00-12:00, 12:30-13:30, 14:00-17:00
# Wednesday: 9:00-9:30, 10:30-13:00, 14:00-17:00
# Thursday: 10:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
mark_busy = {
    0: [(570,660), (690,750), (810,870), (930,960)],
    1: [(540,720), (750,810), (840,1020)],
    2: [(540,570), (630,780), (840,1020)],
    3: [(630,720), (780,810), (840,870), (900,930), (960,1020)]
}

# We need to avoid Wednesday for Evelyn as a preference.
# We'll add a constraint to disallow Wednesday (day == 2).

solution_found = False
selected_day = None
selected_start = None

# Helper: Ensure meeting starting at 'start_var' (lasting 'duration' minutes)
# does not overlap with a busy interval (busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Try candidate days in order (Monday, Tuesday, Wednesday, Thursday)
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add preference: Evelyn would rather not meet on Wednesday.
    if day == 2:
        # Force unsat on Wednesday.
        solver.add(False)  # Skip Wednesday.
    
    # Add Evelyn busy intervals.
    for (busy_start, busy_end) in evelyn_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add Mark busy intervals.
    for (busy_start, busy_end) in mark_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for the earliest valid start time (check minute-by-minute).
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
    # Format the minutes into HH:MM.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")