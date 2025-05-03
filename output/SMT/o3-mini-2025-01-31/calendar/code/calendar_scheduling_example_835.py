from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours in minutes: from 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60   # 540
WORK_END   = 17 * 60  # 1020

# Days are encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Virginia cannot meet on Thursday and Ruth would rather not meet on Monday.
# Hence we restrict the candidates to Tuesday and Wednesday.
candidate_days = [1, 2]  # 1: Tuesday, 2: Wednesday

# Busy intervals for each participant represented as [start, end) in minutes.

# Virginia's busy schedule:
# Monday: 9:00-10:00 (540,600), 12:00-13:00 (720,780), 15:00-15:30 (900,930), 16:30-17:00 (990,1020)
# Tuesday: 10:30-11:30 (630,690), 13:30-14:00 (810,840), 14:30-15:00 (870,900)
# Wednesday: 10:30-11:00 (630,660), 13:30-14:30 (810,870), 15:00-15:30 (900,930), 16:30-17:00 (990,1020)
# Thursday: 9:00-10:00 (540,600), 10:30-12:00 (630,720), 13:00-14:00 (780,840), 15:00-17:00 (900,1020)
virginia_busy = {
    0: [(540,600), (720,780), (900,930), (990,1020)],
    1: [(630,690), (810,840), (870,900)],
    2: [(630,660), (810,870), (900,930), (990,1020)],
    3: [(540,600), (630,720), (780,840), (900,1020)]
}

# Ruth's busy schedule:
# Monday: 9:00-9:30 (540,570), 10:00-10:30 (600,630), 11:00-12:30 (660,750), 
#         13:30-14:00 (810,840), 14:30-17:00 (870,1020)
# Tuesday: 9:00-9:30 (540,570), 11:30-13:00 (690,780), 13:30-15:00 (810,900), 15:30-16:00 (930,960)
# Wednesday: 9:00-10:00 (540,600), 10:30-13:30 (630,810), 14:00-14:30 (840,870),
#            15:00-15:30 (900,930), 16:00-17:00 (960,1020)
# Thursday: 9:00-10:00 (540,600), 10:30-11:00 (630,660), 12:00-13:30 (720,810),
#           14:00-15:00 (840,900), 16:30-17:00 (990,1020)
ruth_busy = {
    0: [(540,570), (600,630), (660,750), (810,840), (870,1020)],
    1: [(540,570), (690,780), (810,900), (930,960)],
    2: [(540,600), (630,810), (840,870), (900,930), (960,1020)],
    3: [(540,600), (630,660), (720,810), (840,900), (990,1020)]
}

# Function that returns a Z3 constraint stating that a meeting starting at time s (lasting duration minutes)
# does not overlap with a busy interval [b_start, b_end).
def no_overlap(b_start, b_end, s):
    # Either the meeting ends before the busy interval starts or starts after the busy interval ends.
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate through candidate days in order (earliest availability first).
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes
    
    # The meeting must fit completely within working hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add Virginia's busy intervals constraints for the given day.
    for (b_start, b_end) in virginia_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add Ruth's busy intervals constraints for the given day.
    for (b_start, b_end) in ruth_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Check each minute in the working hours to find the earliest valid starting time.
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
    # Format the start and end time in HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")