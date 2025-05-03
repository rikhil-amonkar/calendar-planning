from z3 import Solver, Int, Or, sat

# Meeting duration is 30 minutes.
duration = 30

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes).
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# We'll use the following day encoding: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Given the preferences:
# - Janice would like to avoid more meetings on Tuesday after 13:30.
# - Sharon would like to avoid more meetings on Monday and Wednesday.
# Therefore, even though the meeting must fall on one of Monday, Tuesday, Wednesday, or Thursday,
# we restrict our candidate days to Tuesday and Thursday.
candidate_days = [1, 3]  # Tuesday, Thursday

# Janice's busy schedule (times given in minutes from midnight):
# Monday:
#   10:00-10:30 -> (600, 630)
#   11:30-12:00 -> (690, 720)
#   14:30-15:30 -> (870, 930)
#   16:30-17:00 -> (990, 1020)
# Tuesday:
#   10:30-11:00 -> (630, 660)
#   13:00-13:30 -> (780, 810)
#   14:00-14:30 -> (840, 870)
#   16:30-17:00 -> (990, 1020)
# Wednesday:
#   9:30-10:30 -> (570, 630)
# Thursday:
#   9:00-9:30   -> (540, 570)
#   11:00-11:30 -> (660, 690)
#   16:00-16:30 -> (960, 990)
janice_busy = {
    0: [(600,630), (690,720), (870,930), (990,1020)],
    1: [(630,660), (780,810), (840,870), (990,1020)],
    2: [(570,630)],
    3: [(540,570), (660,690), (960,990)]
}

# Sharon's busy schedule:
# Monday:
#   9:00-9:30   -> (540,570)
#   10:00-10:30 -> (600,630)
#   11:00-15:00 -> (660,900)
#   15:30-17:00 -> (930,1020)
# Tuesday:
#   9:30-10:30 -> (570,630)
#   11:00-12:00 -> (660,720)
#   12:30-13:30 -> (750,810)
#   15:00-16:00 -> (900,960)
#   16:30-17:00 -> (990,1020)
# Wednesday:
#   9:00-11:00 -> (540,660)
#   11:30-12:00 -> (690,720)
#   13:00-15:00 -> (780,900)
#   15:30-17:00 -> (930,1020)
# Thursday:
#   9:00-17:00 -> (540,1020)
sharon_busy = {
    0: [(540,570), (600,630), (660,900), (930,1020)],
    1: [(570,630), (660,720), (750,810), (900,960), (990,1020)],
    2: [(540,660), (690,720), (780,900), (930,1020)],
    3: [(540,1020)]
}

# Additional participant preferences:
# - Janice prefers that on Tuesday the meeting finishes by 13:30 (i.e. s+duration <= 13:30 or 810 minutes).
# - Sharon prefers not to have more meetings on Monday or Wednesday;
#   hence we do not consider Monday (0) or Wednesday (2) as candidate days.

# Utility function: Given a busy interval [busy_start, busy_end) and a meeting starting time s (lasting 'duration' minutes),
# the meeting does not overlap the busy interval if it finishes before the busy interval starts or starts after it ends.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over the candidate days in order
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time (in minutes from midnight)
    
    # The meeting must be completely within the work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Apply additional preference for Janice on Tuesday: meeting must finish by 13:30 (810 minutes).
    if day == 1:  # Tuesday
        solver.add(s + duration <= 13 * 60 + 30)  # 13:30 is 810 minutes
    
    # Add Janice's busy intervals for the day.
    for busy_start, busy_end in janice_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add Sharon's busy intervals for the day.
    for busy_start, busy_end in sharon_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Now iterate (minute by minute) to find the earliest valid start time on that day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
        if solver.check() == sat:
            selected_day = day
            selected_start = t
            solution_found = True
            solver.pop()
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes back to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
          day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")