from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours in minutes (from midnight): 9:00 is 540, 17:00 is 1020.
WORK_START = 9 * 60
WORK_END = 17 * 60

# We will consider the meeting on one of the four days:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedule for Dorothy:
# Monday: 16:30 to 17:00    => (990, 1020)
# Tuesday: 10:00 to 10:30   => (600, 630)
# Thursday: 9:00 to 9:30, 13:00 to 13:30  => (540, 570), (780, 810)
dorothy_busy = {
    0: [(990, 1020)],
    1: [(600, 630)],
    2: [],  # No meetings on Wednesday mentioned.
    3: [(540, 570), (780, 810)]
}

# Busy schedule for Judith:
# Monday: 9:00 to 17:00     => (540, 1020)
# Tuesday: 9:00 to 17:00    => (540, 1020)
# Wednesday: 9:00 to 11:00, 12:00 to 17:00  => (540, 660) and (720, 1020)
# Thursday: 9:00 to 10:00, 10:30 to 14:30, 15:00 to 17:00  => (540, 600), (630, 870), (900, 1020)
judith_busy = {
    0: [(540, 1020)],
    1: [(540, 1020)],
    2: [(540, 660), (720, 1020)],
    3: [(540, 600), (630, 870), (900, 1020)]
}

# Helper function to ensure our meeting [start, start+duration) does not overlap a busy interval.
def non_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days
for day in candidate_days:
    solver = Solver()
    
    # Create an integer variable for meeting start time (in minutes from midnight).
    start = Int("start")
    
    # The meeting must be scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add constraints for Dorothy's busy intervals on this day.
    for busy_interval in dorothy_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    # Add constraints for Judith's busy intervals on this day.
    for busy_interval in judith_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    if solver.check() == sat:
        m = solver.model()
        selected_start = m[start].as_long()
        selected_day = day
        solution_found = True
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes into HH:MM format.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")