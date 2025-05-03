from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes (1 hour)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Create a Z3 integer variable for the meeting start time (in minutes from midnight)
start = Int("start")

# Candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Pamela does not want Tuesday, so we will skip day=1.
candidate_days = [0, 1, 2]

# Pamela's busy times (in minutes from midnight):
# Monday: 9:00-9:30 -> (540,570), 10:00-10:30 -> (600,630), 12:00-12:30 -> (720,750), 13:30-14:00 -> (810,840), 15:00-16:00 -> (900,960)
# Tuesday: 10:00-11:00 -> (600,660), 13:30-14:00 -> (810,840), 14:30-15:00 -> (870,900), 16:30-17:00 -> (990,1020)
# Wednesday: 9:00-10:00 -> (540,600), 11:00-11:30 -> (660,690), 13:00-14:00 -> (780,840), 15:30-16:00 -> (930,960), 16:30-17:00 -> (990,1020)
pamela_busy = {
    0: [(540, 570), (600, 630), (720, 750), (810, 840), (900, 960)],
    1: [(600, 660), (810, 840), (870, 900), (990, 1020)],
    2: [(540, 600), (660, 690), (780, 840), (930, 960), (990, 1020)]
}

# Judith's busy times:
# Monday: 9:00-9:30 -> (540,570), 11:00-11:30 -> (660,690), 12:00-15:30 -> (720,930), 16:30-17:00 -> (990,1020)
# Tuesday: 9:30-11:00 -> (570,660), 12:00-12:30 -> (720,750), 15:00-15:30 -> (900,930)
# Wednesday: 11:00-13:30 -> (660,810), 14:00-14:30 -> (840,870), 15:00-15:30 -> (900,930), 16:00-17:00 -> (960,1020)
judith_busy = {
    0: [(540, 570), (660, 690), (720, 930), (990, 1020)],
    1: [(570, 660), (720, 750), (900, 930)],
    2: [(660, 810), (840, 870), (900, 930), (960, 1020)]
}

# Helper function:
# Ensures that the meeting interval [start, start+duration) does not overlap a busy interval [b_start, b_end).
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Check each candidate day
for day in candidate_days:
    # Pamela does NOT want to meet on Tuesday (day 1)
    if day == 1:
        continue

    solver = Solver()
    
    # Meeting must be scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Pamela's busy time constraints for the chosen day.
    for (b_start, b_end) in pamela_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Judith's busy time constraints for the chosen day.
    for (b_start, b_end) in judith_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try every possible start minute in the workday.
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