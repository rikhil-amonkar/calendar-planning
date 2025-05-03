from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540
WORK_END = 17 * 60    # 1020

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Julie has no meetings, so no busy schedule for her.
# However, Julie would like to avoid meetings on Thursday before 11:30.
# We will interpret this as an additional constraint if the meeting is on Thursday.

# Ruth's busy schedule (times in minutes from midnight):
# Monday: 9:00 to 17:00 -> (540, 1020)
# Tuesday: 9:00 to 17:00 -> (540, 1020)
# Wednesday: 9:00 to 17:00 -> (540, 1020)
# Thursday: busy intervals:
#    9:00 to 11:00   -> (540, 660)
#    11:30 to 14:30  -> (690, 870)
#    15:00 to 17:00  -> (900, 1020)
ruth_busy = {
    0: [(540, 1020)],
    1: [(540, 1020)],
    2: [(540, 1020)],
    3: [(540, 660), (690, 870), (900, 1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function: meeting (starting at start_var for 'duration' minutes) does not overlap a busy interval.
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate over candidate days:
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # Meeting must fall within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Julie has a preference on Thursday: avoid meetings before 11:30 (i.e., meeting must start at or after 11:30)
    if day == 3:
        solver.add(start >= 11 * 60 + 30)  # 11:30 is 690 minutes
    
    # Ruth's busy constraints on the given day.
    for (busy_start, busy_end) in ruth_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for an available time on this day (iterate minute-by-minute)
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