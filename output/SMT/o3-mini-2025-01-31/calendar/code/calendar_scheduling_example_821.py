from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Wayne's busy schedule (times as minutes from midnight):
# Monday: 9:30-10:00 -> (570,600)
# Wednesday: 12:30-13:00 -> (750,780)
# Thursday: 10:30-11:30 -> (630,690)
wayne_busy = {
    0: [(570, 600)],
    2: [(750, 780)],
    3: [(630, 690)]
}

# Ronald's busy schedule:
# Monday: 9:00-12:00 -> (540,720); 12:30-14:30 -> (750,870); 15:00-16:30 -> (900,990)
# Tuesday: 9:30-10:30 -> (570,630); 12:00-13:00 -> (720,780); 14:00-17:00 -> (840,1020)
# Wednesday: 9:30-10:00 -> (570,600); 10:30-11:00 -> (630,660); 11:30-14:00 -> (690,840);
#            14:30-15:00 -> (870,900); 15:30-17:00 -> (930,1020)
# Thursday: 9:00-17:00 -> (540,1020)
ronald_busy = {
    0: [(540,720), (750,870), (900,990)],
    1: [(570,630), (720,780), (840,1020)],
    2: [(570,600), (630,660), (690,840), (870,900), (930,1020)],
    3: [(540,1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper: ensures that a meeting starting at 'start_var' for 'duration' minutes
# does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate over candidate days.
# Additional preferences:
#   - Wayne would like to avoid more meetings on Monday before 16:30.
#     (i.e. if meeting is on Monday, it must start at or after 16:30, which is 990 minutes)
#   - Ronald does not want to meet on Wednesday.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Wayne's preference: on Monday, avoid meetings before 16:30.
    if day == 0:
        solver.add(start >= 16 * 60 + 30)  # 16:30 -> 990 minutes
        
    # Ronald's preference: do not meet on Wednesday.
    if day == 2:
        solver.add(False)  # Disallow Wednesday
    
    # Add Wayne's busy time constraints.
    for (busy_start, busy_end) in wayne_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add Ronald's busy time constraints.
    for (busy_start, busy_end) in ronald_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Check for a valid start time minute-by-minute within work hours.
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