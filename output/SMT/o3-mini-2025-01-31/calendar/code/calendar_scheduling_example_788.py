from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (half an hour)
duration = 30

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Create a Z3 integer variable for the meeting start time (in minutes from midnight)
start = Int("start")

# Encode days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# We will try to schedule on these days in order (to get the earliest available overall).
candidate_days = [0, 1, 2]

# Kimberly's busy schedule (in minutes from midnight)
# Monday:
#   9:30 to 10:30 -> (570, 630)
#   11:00 to 11:30 -> (660, 690)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:00 -> (930, 960)
# Wednesday:
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:00 -> (690, 720)
#   13:00 to 14:00 -> (780, 840)
#   15:00 to 15:30 -> (900, 930)
kimberly_busy = {
    0: [(570, 630), (660, 690), (960, 990)],
    1: [(810, 840), (870, 900), (930, 960)],
    2: [(600, 630), (690, 720), (780, 840), (900, 930)]
}

# Diane's busy schedule (in minutes from midnight)
# Monday:
#   9:30 to 12:00 -> (570, 720)
#   12:30 to 14:30 -> (750, 870)
#   15:00 to 15:30 -> (900, 930)
# Tuesday:
#   9:00 to 17:00 -> (540, 1020)
# Wednesday:
#   9:00 to 17:00 -> (540, 1020)
diane_busy = {
    0: [(570, 720), (750, 870), (900, 930)],
    1: [(540, 1020)],
    2: [(540, 1020)]
}

# Helper function: For a busy interval (b_start, b_end) the meeting interval [start, start+duration)
# must not overlap this busy interval.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order: Monday (0), then Tuesday (1), then Wednesday (2)
for day in candidate_days:
    solver = Solver()
    # The meeting must start no earlier than work start and finish by work end.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Kimberly's busy constraints for the day.
    for (b_start, b_end) in kimberly_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Diane's busy constraints for the day.
    for (b_start, b_end) in diane_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Since the group prefers the earliest available slot,
    # we iterate minute-by-minute from WORK_START to the last possible start time.
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
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")