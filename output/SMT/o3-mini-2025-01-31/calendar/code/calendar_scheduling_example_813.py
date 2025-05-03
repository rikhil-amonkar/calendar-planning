from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes (1 hour).
duration = 60

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes).
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Brenda has no meetings all week.
# Justin's busy schedule in minutes (from midnight):
# Monday: 9:30-10:00, 11:00-12:00, 13:00-14:00, 14:30-15:30, 16:00-17:00.
# Tuesday: 9:30-10:00, 10:30-11:00, 12:30-14:30, 15:00-15:30, 16:30-17:00.
# Wednesday: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:30-13:00, 14:00-15:30, 16:30-17:00.
# Thursday: 9:00-10:00, 10:30-11:00, 12:30-14:00, 15:00-15:30.
justin_busy = {
    0: [(570,600), (660,720), (780,840), (870,930), (960,1020)],
    1: [(570,600), (630,660), (750,870), (900,930), (990,1020)],
    2: [(540,570), (600,630), (660,690), (750,780), (840,930), (990,1020)],
    3: [(540,600), (630,660), (750,840), (900,930)]
}

# The group would like to meet at their earliest availability.
solution_found = False
selected_day = None
selected_start = None

# Helper function: Ensure a meeting starting at 'start_var' (lasting 'duration' minutes)
# does not overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate through candidate days in order
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Since Brenda is free, we only add Justin's busy intervals.
    for (busy_start, busy_end) in justin_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Iterate over possible start times minute-by-minute for earliest availability.
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