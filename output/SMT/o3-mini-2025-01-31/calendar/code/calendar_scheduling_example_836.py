from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END = 17 * 60     # 1020 minutes

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Busy intervals for each participant, represented as [start, end) in minutes

# Melissa's busy schedule:
# Monday: 11:00-11:30 (660,690), 13:00-13:30 (780,810),
#         14:30-15:00 (870,900), 15:30-16:30 (930,990)
# Tuesday: 9:30-10:00 (570,600), 11:30-12:00 (690,720),
#          13:00-13:30 (780,810), 15:00-15:30 (900,930)
# Wednesday: 13:30-14:00 (810,840), 14:30-15:00 (870,900)
# Thursday: 9:00-9:30 (540,570), 10:30-11:00 (630,660),
#           13:00-13:30 (780,810), 15:30-16:00 (930,960), 16:30-17:00 (990,1020)
melissa_busy = {
    0: [(660, 690), (780, 810), (870, 900), (930, 990)],
    1: [(570, 600), (690, 720), (780, 810), (900, 930)],
    2: [(810, 840), (870, 900)],
    3: [(540, 570), (630, 660), (780, 810), (930, 960), (990, 1020)]
}

# Richard's busy schedule:
# Monday: 9:00-10:30 (540,630), 11:00-12:30 (660,750), 
#         13:00-13:30 (780,810), 14:00-15:00 (840,900), 16:00-17:00 (960,1020)
# Tuesday: 9:30-10:00 (570,600), 10:30-12:30 (630,750), 
#          13:30-14:00 (810,840), 14:30-15:00 (870,900), 15:30-17:00 (930,1020)
# Wednesday: 9:00-9:30 (540,570), 10:00-10:30 (600,630), 
#            11:00-13:00 (660,780), 14:00-15:00 (840,900), 16:00-16:30 (960,990)
# Thursday: 9:00-10:00 (540,600), 10:30-11:00 (630,660), 
#           11:30-13:00 (690,780), 13:30-15:00 (810,900), 15:30-17:00 (930,1020)
richard_busy = {
    0: [(540, 630), (660, 750), (780, 810), (840, 900), (960, 1020)],
    1: [(570, 600), (630, 750), (810, 840), (870, 900), (930, 1020)],
    2: [(540, 570), (600, 630), (660, 780), (840, 900), (960, 990)],
    3: [(540, 600), (630, 660), (690, 780), (810, 900), (930, 1020)]
}

# Utility function: given a busy interval [b_start, b_end) and a meeting start time s,
# ensure that the meeting (lasting 'duration') does not overlap with the interval.
def no_overlap(b_start, b_end, s):
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days (Monday, Tuesday, Wednesday, Thursday) in order.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes
    
    # The meeting must be entirely within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add Melissa's busy intervals constraints for the current day.
    for (b_start, b_end) in melissa_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add Richard's busy intervals constraints for the current day.
    for (b_start, b_end) in richard_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Find the earliest possible meeting start time by checking every minute.
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
    # Convert minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")