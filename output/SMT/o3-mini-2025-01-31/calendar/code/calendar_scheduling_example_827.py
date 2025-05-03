from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Candidate days: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Angela's busy intervals (in minutes) by day:
# Monday: 13:30 to 14:00 --> (810, 840)
# Tuesday: 9:00 to 9:30 --> (540, 570) and 10:00 to 10:30 --> (600, 630)
# Wednesday: no meetings
# Thursday: 15:30 to 16:00 --> (930, 960)
angela_busy = {
    0: [(810, 840)],
    1: [(540, 570), (600, 630)],
    2: [],
    3: [(930, 960)]
}

# Patrick's busy intervals (in minutes) by day:
# Monday: 9:30 to 10:30 --> (570,630), 11:00 to 12:30 --> (660,750),
#         13:30 to 14:00 --> (810,840), 15:30 to 17:00 --> (930,1020)
# Tuesday: 9:00 to 12:30 --> (540,750), 13:00 to 14:00 --> (780,840),
#          15:00 to 16:00 --> (900,960), 16:30 to 17:00 --> (990,1020)
# Wednesday: 9:00 to 11:00 --> (540,660), 12:00 to 13:00 --> (720,780),
#            13:30 to 17:00 --> (810,1020)
# Thursday: 9:00 to 9:30 --> (540,570), 10:00 to 11:00 --> (600,660),
#           11:30 to 12:00 --> (690,720), 13:00 to 13:30 --> (780,810),
#           14:00 to 15:00 --> (840,900), 15:30 to 17:00 --> (930,1020)
patrick_busy = {
    0: [(570,630), (660,750), (810,840), (930,1020)],
    1: [(540,750), (780,840), (900,960), (990,1020)],
    2: [(540,660), (720,780), (810,1020)],
    3: [(540,570), (600,660), (690,720), (780,810), (840,900), (930,1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function: ensures that a meeting starting at 'start_var' (lasting 'duration')
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# According to constraints, Patrick cannot meet on Monday.
# We want the meeting at the earliest availability.
# We'll iterate over candidate days in order (Monday, Tuesday, Wednesday, Thursday)
# and check minute-by-minute from WORK_START to WORK_END - duration.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    # Meeting must happen within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Enforce that Patrick cannot meet on Monday.
    if day == 0:
        solver.add(False)
    
    # Add Angela's busy intervals for the day.
    for (b_start, b_end) in angela_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Add Patrick's busy intervals for the day.
    for (b_start, b_end) in patrick_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Check each minute possibility for the meeting start.
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