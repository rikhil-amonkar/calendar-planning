from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Workday from 9:00 (540 minutes) to 17:00 (1020 minutes).
WORK_START = 9 * 60     # 540
WORK_END   = 17 * 60    # 1020

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedules for Mary:
# Tuesday: 10:00-10:30 (600,630), 15:30-16:00 (930,960)
# Wednesday: 9:30-10:00 (570,600), 15:00-15:30 (900,930)
# Thursday: 9:00-10:00 (540,600), 10:30-11:30 (630,690)
mary_busy = {
    1: [(600, 630), (930, 960)],
    2: [(570, 600), (900, 930)],
    3: [(540, 600), (630, 690)]
}

# Busy schedules for Alexis:
# Monday: 9:00-10:00 (540,600), 10:30-12:00 (630,720), 12:30-16:30 (750,990)
# Tuesday: 9:00-10:00 (540,600), 10:30-11:30 (630,690), 12:00-15:30 (720,930), 16:00-17:00 (960,1020)
# Wednesday: 9:00-11:00 (540,660), 11:30-17:00 (690,1020)
# Thursday: 10:00-12:00 (600,720), 14:00-14:30 (840,870), 15:30-16:00 (930,960), 16:30-17:00 (990,1020)
alexis_busy = {
    0: [(540,600), (630,720), (750,990)],
    1: [(540,600), (630,690), (720,930), (960,1020)],
    2: [(540,660), (690,1020)],
    3: [(600,720), (840,870), (930,960), (990,1020)]
}

# The group wants to meet at their earliest availability;
# so we try days in order (Monday first) and then the earliest start time.

solution_found = False
selected_day = None
selected_start = None

# Define helper to ensure a meeting starting at 'start_var' (lasting for 'duration')
# does not overlap with a busy interval defined by (busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Search candidate days in order
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)

    # Add Mary's busy intervals (if any) for the current day.
    for (busy_start, busy_end) in mary_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add Alexis's busy intervals (if any) for the current day.
    for (busy_start, busy_end) in alexis_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Try to find the earliest available start time by iterating minute-by-minute.
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