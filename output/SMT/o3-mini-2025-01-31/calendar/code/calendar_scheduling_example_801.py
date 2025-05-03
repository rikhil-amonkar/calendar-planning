from z3 import Solver, Int, Or, sat

# Meeting duration is 30 minutes.
duration = 30

# Work hours in minutes from midnight: 9:00 is 540, 17:00 is 1020.
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define the start time variable (in minutes from midnight).
start = Int("start")

# Candidate days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Busy schedules for Sarah (intervals are in (start, end) in minutes)
sarah_busy = {
    0: [(570, 600), (630, 660), (720, 840), (900, 1020)],                # Monday
    1: [(780, 810), (840, 870), (900, 930), (960, 1020)],                # Tuesday
    2: [(540, 630), (660, 690), (750, 780), (810, 870), (900, 960), (990, 1020)],  # Wednesday
    3: [(540, 570), (780, 810), (900, 990)]                               # Thursday
}

# Busy schedules for Peter (intervals are in (start, end) in minutes)
peter_busy = {
    0: [(540, 600), (660, 720), (780, 810), (840, 990)],                # Monday
    1: [(540, 570), (630, 690), (780, 810), (840, 900), (990, 1020)],      # Tuesday
    2: [(600, 630), (690, 720), (810, 840), (870, 900), (960, 990)],       # Wednesday
    3: [(540, 840), (870, 900), (930, 1020)]                              # Thursday
}

# Helper function to ensure the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# We'll explore days in order, trying to find the earliest valid start time.
for day in candidate_days:
    solver = Solver()
    # The meeting must fall entirely within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Sarah's busy constraints for the current day.
    for busy_interval in sarah_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Peter's busy constraints for the current day.
    for busy_interval in peter_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # For each minute in the work day, check if the meeting can start then.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Clean up the solver state.
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")