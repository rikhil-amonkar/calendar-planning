from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Ashley's busy schedule (times in minutes from midnight):
# Monday: 9:00-9:30 -> (540,570), 10:00-11:30 -> (600,690), 13:30-14:00 -> (810,840),
#         15:00-15:30 -> (900,930), 16:00-16:30 -> (960,990)
# Tuesday: 9:30-11:00 -> (570,660), 14:00-14:30 -> (840,870), 16:30-17:00 -> (990,1020)
# Wednesday: 9:00-10:00 -> (540,600), 11:00-12:30 -> (660,750), 13:00-13:30 -> (780,810),
#            14:30-15:00 -> (870,900), 15:30-16:30 -> (930,990)
# Thursday: 9:00-10:00 -> (540,600), 12:30-13:30 -> (750,810), 14:30-15:00 -> (870,900)
ashley_busy = {
    0: [(540,570), (600,690), (810,840), (900,930), (960,990)],
    1: [(570,660), (840,870), (990,1020)],
    2: [(540,600), (660,750), (780,810), (870,900), (930,990)],
    3: [(540,600), (750,810), (870,900)]
}

# Gloria's busy schedule (times in minutes from midnight):
# Monday: 9:00-17:00 -> (540,1020)
# Tuesday: 10:00-11:00 -> (600,660), 11:30-12:00 -> (690,720), 
#          13:00-16:00 -> (780,960), 16:30-17:00 -> (990,1020)
# Wednesday: 9:00-10:00 -> (540,600), 11:00-11:30 -> (660,690), 
#            12:00-12:30 -> (720,750), 13:30-16:30 -> (810,990)
# Thursday: 9:00-11:00 -> (540,660), 12:00-14:00 -> (720,840), 
#           14:30-16:00 -> (870,960), 16:30-17:00 -> (990,1020)
gloria_busy = {
    0: [(540,1020)],
    1: [(600,660), (690,720), (780,960), (990,1020)],
    2: [(540,600), (660,690), (720,750), (810,990)],
    3: [(540,660), (720,840), (870,960), (990,1020)]
}

# Utility function: ensure that the meeting (from s to s+duration)
# does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days (Monday, Tuesday, Wednesday, Thursday)
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes
    
    # Meeting must lie within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add constraints for Ashley's busy times for the given day.
    for (b_start, b_end) in ashley_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add constraints for Gloria's busy times for the given day.
    for (b_start, b_end) in gloria_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Try every possible start minute in the workday and pick the earliest valid one.
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
    # Convert minutes to HH:MM
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")