from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (1 hour)
duration = 60

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Create a Z3 integer variable for the meeting start time (in minutes from midnight)
start = Int("start")

# Encode days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# We'll try candidate days in order: Monday, then Tuesday, then Wednesday.
candidate_days = [0, 1, 2]

# Arthur's busy schedule (busy intervals are represented in minutes from midnight)
# Monday:
#   9:30 to 10:00 -> (570, 600)
#   10:30 to 11:30 -> (630, 690)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 14:00 -> (810, 840)
# Tuesday:
#   10:00 to 11:30 -> (600, 690)
#   16:30 to 17:00 -> (990, 1020)
# Wednesday:
#   9:00 to 10:00   -> (540, 600)
#   11:30 to 12:00  -> (690, 720)
#   13:30 to 14:00  -> (810, 840)
#   14:30 to 15:30  -> (870, 930)
#   16:30 to 17:00  -> (990, 1020)
arthur_busy = {
    0: [(570, 600), (630, 690), (750, 780), (810, 840)],
    1: [(600, 690), (990, 1020)],
    2: [(540, 600), (690, 720), (810, 840), (870, 930), (990, 1020)]
}

# Robert's busy schedule:
# Monday:
#   9:00 to 9:30   -> (540, 570)
#   12:00 to 12:30 -> (720, 750)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:30 -> (930, 990)
# Tuesday:
#   9:00 to 10:30  -> (540, 630)
#   11:30 to 13:00 -> (690, 780)
#   13:30 to 15:30 -> (810, 930)
#   16:00 to 16:30 -> (960, 990)
# Wednesday:
#   9:00 to 10:30  -> (540, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 15:00 -> (810, 900)
robert_busy = {
    0: [(540, 570), (720, 750), (870, 900), (930, 990)],
    1: [(540, 630), (690, 780), (810, 930), (960, 990)],
    2: [(540, 630), (660, 690), (720, 750), (810, 900)]
}

# Robert prefers to avoid having meetings on Wednesday before 14:00.
# We interpret this as a constraint when scheduling on Wednesday:
#   if day == 2 then start must be at least 14:00 (840 minutes)
WEDNESDAY_MIN_START = 14 * 60  # 840 minutes

# Helper function: Given a busy interval (b_start, b_end), 
# the meeting interval [start, start+duration) must not overlap it.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order: Monday (0), Tuesday (1), then Wednesday (2)
for day in candidate_days:
    solver = Solver()
    # The meeting must finish by work end and start no earlier than work start.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Arthur's busy constraints for the day.
    for (b_start, b_end) in arthur_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Robert's busy constraints for the day.
    for (b_start, b_end) in robert_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # If the day is Wednesday, enforce Robert's preference: meeting should not start before 14:00.
    if day == 2:
        solver.add(start >= WEDNESDAY_MIN_START)
    
    # Search for the earliest valid starting time (minute by minute).
    # Latest possible start is WORK_END - duration.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # clean up before breaking out
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes into HH:MM strings.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")