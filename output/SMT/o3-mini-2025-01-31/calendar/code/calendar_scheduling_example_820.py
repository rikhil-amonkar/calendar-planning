from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Evelyn's busy schedule (times in minutes from midnight):
# Monday: 10:00-10:30 -> (600,630); 11:00-11:30 -> (660,690);
#         13:00-14:00 -> (780,840); 14:30-16:00 -> (870,960); 16:30-17:00 -> (990,1020)
# Tuesday: 10:30-11:00 -> (630,660); 12:30-13:00 -> (750,780); 14:30-15:30 -> (870,930)
# Wednesday: 10:00-10:30 -> (600,630); 13:30-14:30 -> (810,870); 16:30-17:00 -> (990,1020)
# Thursday: 10:00-10:30 -> (600,630); 11:30-12:00 -> (690,720); 12:30-13:30 -> (750,810)
evelyn_busy = {
    0: [(600, 630), (660, 690), (780, 840), (870, 960), (990, 1020)],
    1: [(630, 660), (750, 780), (870, 930)],
    2: [(600, 630), (810, 870), (990, 1020)],
    3: [(600, 630), (690, 720), (750, 810)]
}

# Nancy's busy schedule:
# Monday: 9:30 to 17:00 -> (570,1020)
# Tuesday: 9:00-9:30 -> (540,570); 10:00-12:30 -> (600,750);
#          13:00-14:00 -> (780,840); 14:30-15:00 -> (870,900);
#          15:30-16:30 -> (930,990)
# Wednesday: 9:30-10:00 -> (570,600); 10:30-11:00 -> (630,660);
#            13:00-13:30 -> (780,810); 14:00-15:30 -> (840,930);
#            16:30-17:00 -> (990,1020)
# Thursday: 9:30-10:00 -> (570,600); 11:00-14:00 -> (660,840);
#           15:00-15:30 -> (900,930); 16:00-16:30 -> (960,990)
nancy_busy = {
    0: [(570, 1020)],
    1: [(540,570), (600,750), (780,840), (870,900), (930,990)],
    2: [(570,600), (630,660), (780,810), (840,930), (990,1020)],
    3: [(570,600), (660,840), (900,930), (960,990)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper: ensures that a meeting starting at 'start_var' for 'duration'
# minutes does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate over candidate days.
# Evelyn would like to avoid more meetings on Wednesday.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    # meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Preference: Evelyn would prefer not to have meetings on Wednesday.
    if day == 2:
        solver.add(False)  # Disallow Wednesday
    
    # Add Evelyn's busy constraints.
    for (busy_start, busy_end) in evelyn_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add Nancy's busy constraints.
    for (busy_start, busy_end) in nancy_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Check minute-by-minute within work hours for a valid start.
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