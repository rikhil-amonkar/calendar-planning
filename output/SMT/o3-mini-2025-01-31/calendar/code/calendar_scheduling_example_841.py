from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60      # 540 minutes
WORK_END = 17 * 60       # 1020 minutes

# Encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# We will check candidate days in order.
candidate_days = [0, 1, 2, 3]

# Susan's busy schedule (times in minutes from midnight):
# Monday: 14:00 to 14:30   -> (840, 870)
# Tuesday: 9:30 to 10:00   -> (570, 600), and 16:00 to 16:30 -> (960, 990)
# Wednesday: 11:00 to 12:00 -> (660, 720), 15:00 to 16:00 -> (900, 960), 16:30 to 17:00 -> (990,1020)
# Thursday: 12:00 to 13:00  -> (720, 780), 14:30 to 15:00 -> (870, 900), 16:30 to 17:00 -> (990,1020)
susan_busy = {
    0: [(840, 870)],
    1: [(570, 600), (960, 990)],
    2: [(660, 720), (900, 960), (990, 1020)],
    3: [(720, 780), (870, 900), (990, 1020)]
}

# Aaron's busy schedule (times in minutes from midnight):
# Monday: 9:00 to 10:30   -> (540, 630), 11:00 to 16:00 -> (660, 960), 16:30 to 17:00 -> (990,1020)
# Tuesday: 9:00 to 17:00   -> (540, 1020)
# Wednesday: 9:00 to 17:00 -> (540, 1020)
# Thursday: 9:00 to 17:00  -> (540, 1020)
aaron_busy = {
    0: [(540, 630), (660, 960), (990, 1020)],
    1: [(540, 1020)],
    2: [(540, 1020)],
    3: [(540, 1020)]
}

# Additional preference: Susan would rather not meet on Monday after 11:00.
# We interpret this as: if the meeting is on Monday (day 0),
# then the meeting must end no later than 11:00 (i.e., meeting start + duration <= 11:00).
def add_monday_preference(day, s):
    if day == 0:
        return s + duration <= 11 * 60  # 11:00 = 660 minutes
    return True

# Utility: ensure meeting (from s to s+duration) does NOT overlap a busy interval [b_start, b_end)
def no_overlap(b_start, b_end, s):
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate through candidate days in order
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time (in minutes)
    
    # Meeting must be within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add additional preference for Monday if applicable.
    solver.add(add_monday_preference(day, s))
    
    # Add Susan's busy time constraints.
    for (b_start, b_end) in susan_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add Aaron's busy time constraints.
    for (b_start, b_end) in aaron_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Try every possible start minute and pick the earliest one that satisfies constraints.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
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
    # Convert minutes to HH:MM format
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")