from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours in minutes (from midnight): 9:00 is 540, 17:00 is 1020.
WORK_START = 9 * 60
WORK_END = 17 * 60

# Days are represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]  # in order: Monday, Tuesday, Wednesday, Thursday

# Busy schedule for Tyler
# Monday: 11:00-11:30, 13:00-13:30, 15:00-15:30
# Tuesday: 10:30-11:00, 11:30-12:00, 13:30-14:00, 16:30-17:00
# Wednesday: 9:00-9:30, 10:00-10:30, 13:00-14:00
# Thursday: 11:30-12:00, 12:30-13:00, 13:30-14:00
tyler_busy = {
    0: [(660, 690), (780, 810), (900, 930)],
    1: [(630, 660), (690, 720), (810, 840), (990, 1020)],
    2: [(540, 570), (600, 630), (780, 840)],
    3: [(690, 720), (750, 780), (810, 840)]
}

# Busy schedule for Jack
# Monday: 9:00-10:00, 11:00-11:30, 12:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
# Tuesday: 9:00-9:30, 12:00-13:30, 14:00-14:30, 15:30-16:00
# Wednesday: 9:00-10:00, 10:30-13:00, 13:30-15:00, 15:30-16:00
# Thursday: 9:30-11:30, 14:00-14:30
jack_busy = {
    0: [(540, 600), (660, 690), (720, 810), (840, 870), (900, 930), (960, 1020)],
    1: [(540, 570), (720, 810), (840, 870), (930, 960)],
    2: [(540, 600), (630, 780), (810, 900), (930, 960)],
    3: [(570, 690), (840, 870)]
}

# Helper function to create a Z3 constraint ensuring that a meeting scheduled at 'start' (with given duration)
# does not overlap with an interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate through candidate days in order to find the earliest meeting time across the week.
for day in candidate_days:
    solver = Solver()
    # Create an integer variable for the meeting start time (in minutes from midnight).
    start = Int("start")
    # Meeting must lie entirely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add the non-overlap constraints for Tyler's busy intervals on this day.
    for interval in tyler_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    # Add the non-overlap constraints for Jack's busy intervals on this day.
    for interval in jack_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    # Now, we check for the earliest possible start in this day.
    # We iterate minute by minute (from WORK_START to latest possible start) in ascending order.
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