from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Candidate days: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Frances' busy intervals (in minutes) by day:
# Monday: 10:00 to 10:30 -> (600, 630)
# Tuesday: 13:30 to 14:00 -> (810,840); 14:30 to 15:00 -> (870,900)
# Wednesday: 10:00 to 10:30 -> (600,630); 13:00 to 13:30 -> (780,810); 14:00 to 14:30 -> (840,870)
# Thursday: 11:30 to 12:00 -> (690,720); 13:00 to 13:30 -> (780,810); 14:30 to 15:00 -> (870,900); 16:30 to 17:00 -> (990,1020)
frances_busy = {
    0: [(600, 630)],
    1: [(810,840), (870,900)],
    2: [(600,630), (780,810), (840,870)],
    3: [(690,720), (780,810), (870,900), (990,1020)]
}

# Christina's busy intervals (in minutes) by day:
# Monday: 9:00 to 9:30 -> (540,570); 10:00 to 10:30 -> (600,630); 
#         12:30 to 14:30 -> (750,870); 15:30 to 17:00 -> (930,1020)
# Tuesday: 9:00 to 11:30 -> (540,690); 12:00 to 12:30 -> (720,750);
#          13:00 to 15:30 -> (780,930); 16:00 to 17:00 -> (960,1020)
# Wednesday: 9:30 to 10:00 -> (570,600); 10:30 to 11:00 -> (630,660);
#            13:00 to 13:30 -> (780,810); 15:00 to 15:30 -> (900,930);
#            16:00 to 17:00 -> (960,1020)
# Thursday: 9:00 to 10:00 -> (540,600); 10:30 to 12:00 -> (630,720);
#           14:30 to 15:00 -> (870,900)
christina_busy = {
    0: [(540,570), (600,630), (750,870), (930,1020)],
    1: [(540,690), (720,750), (780,930), (960,1020)],
    2: [(570,600), (630,660), (780,810), (900,930), (960,1020)],
    3: [(540,600), (630,720), (870,900)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function that ensures that a meeting starting at 'start_var'
# (lasting 'duration') does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Frances would rather not meet on Wednesday,
# and we want the meeting at the earliest availability.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Frances preference: avoid meeting on Wednesday.
    if day == 2:
        solver.add(False)
    
    # Add Frances busy intervals for the day.
    for (b_start, b_end) in frances_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Add Christina busy intervals for the day.
    for (b_start, b_end) in christina_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Check minute-by-minute for an available starting time.
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