from z3 import Solver, Int, Or, sat

# Meeting duration: one hour (60 minutes)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Create a Z3 integer variable for the meeting start time (in minutes from midnight)
start = Int("start")

# We need to schedule the meeting on Monday, Tuesday, or Wednesday.
# However, Barbara would rather not meet on Tuesday.
# To incorporate this preference, we will check candidate days in a preferred order:
# Monday (0), Wednesday (2), and then Tuesday (1) as a last resort.
candidate_days = [0, 2, 1]

# Busy schedules are represented as intervals in minutes from midnight.

# Barbara's busy times:
# Monday:
#   9:00 to 9:30 -> (540, 570)
#   10:30 to 11:30 -> (630, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 14:30 -> (810, 870)
#   15:00 to 15:30 -> (900, 930)
# Tuesday:
#   9:00 to 9:30 -> (540, 570)
#   10:30 to 11:30 -> (630, 690)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 16:00 -> (900, 960)
# Wednesday:
#   9:00 to 9:30 -> (540, 570)
#   10:30 to 11:00 -> (630, 660)
#   11:30 to 12:00 -> (690, 720)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 14:00 -> (810, 840)
#   16:00 to 16:30 -> (960, 990)
barbara_busy = {
    0: [(540, 570), (630, 690), (720, 750), (810, 870), (900, 930)],
    1: [(540, 570), (630, 690), (750, 780), (810, 840), (900, 960)],
    2: [(540, 570), (630, 660), (690, 720), (750, 780), (810, 840), (960, 990)]
}

# Jason's busy times:
# Monday:
#   10:00 to 12:00 -> (600, 720)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 15:30 -> (810, 930)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   9:00 to 10:30 -> (540, 630)
#   11:30 to 13:00 -> (690, 780)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:00 -> (870, 900)
# Wednesday:
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 13:00 -> (720, 780)
#   13:30 to 14:30 -> (810, 870)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 17:00 -> (960, 1020)
jason_busy = {
    0: [(600, 720), (750, 780), (810, 930), (960, 990)],
    1: [(540, 630), (690, 780), (810, 840), (870, 900)],
    2: [(660, 690), (720, 780), (810, 870), (900, 930), (960, 1020)]
}

# A helper function to express that the meeting interval [start, start+duration)
# does not overlap a busy interval (b_start, b_end).
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in preferred order.
for day in candidate_days:
    solver = Solver()
    
    # The meeting must be entirely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Barbara's busy constraints for the day.
    for (b_start, b_end) in barbara_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Jason's busy constraints for the day.
    for (b_start, b_end) in jason_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # For each candidate day, search minute-by-minute for the earliest available start time.
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