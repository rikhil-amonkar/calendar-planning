from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Melissa's busy schedule (times in minutes from midnight):
# Monday: 9:00-9:30, 10:30-11:00, 12:00-12:30, 13:00-16:30
# Tuesday: 9:00-9:30, 10:00-10:30, 13:30-14:00, 14:30-15:30
# Wednesday: 9:00-9:30, 10:00-11:00, 12:30-13:00, 14:00-14:30, 15:00-15:30
# Thursday: 11:00-11:30, 12:30-13:00, 15:00-15:30
melissa_busy = {
    0: [(540, 570), (630, 660), (720, 750), (780, 990)],
    1: [(540, 570), (600, 630), (810, 840), (870, 930)],
    2: [(540, 570), (600, 660), (750, 780), (840, 870), (900, 930)],
    3: [(660, 690), (750, 780), (900, 930)]
}

# Diane's busy schedule:
# Monday: 9:00-10:00, 10:30-16:30
# Tuesday: 9:00-17:00
# Wednesday: 9:00-17:00
# Thursday: 9:00-17:00
diane_busy = {
    0: [(540, 600), (630, 990)],
    1: [(540, 1020)],
    2: [(540, 1020)],
    3: [(540, 1020)]
}

# Diane would like to avoid more meetings on Monday before 16:00.
# Therefore, if the meeting is scheduled on Monday (day == 0), the meeting must start at or after 16:00 (960 minutes).
PREFERRED_MONDAY_START = 16 * 60  # 960 minutes

solution_found = False
selected_day = None
selected_start = None

# Helper function to enforce that a meeting (starting at start_var for duration minutes)
# does not overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate through candidate days in order: Monday, Tuesday, Wednesday, Thursday.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Monday, enforce Diane's preference (meeting should start no earlier than 16:00)
    if day == 0:
        solver.add(start >= PREFERRED_MONDAY_START)
    
    # Add Melissa's busy constraints for the day.
    for (busy_start, busy_end) in melissa_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add Diane's busy constraints for the day.
    for (busy_start, busy_end) in diane_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for the earliest valid start time (minute-by-minute)
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
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")