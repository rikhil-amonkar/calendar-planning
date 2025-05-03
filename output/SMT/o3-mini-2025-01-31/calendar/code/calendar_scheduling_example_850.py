from z3 import Solver, Int, Or, sat

# Meeting duration is 30 minutes.
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Although the meeting can be on any of these days,
# Nicholas would like to avoid more meetings on Monday.
# In addition, Virginia is fully booked on Wednesday and Thursday.
# So we favor Tuesday first and consider Monday only if necessary.
candidate_days = [1, 0]  # Tuesday then Monday

# Nicholas's busy schedule (times in minutes from midnight):
# Monday:
#   9:00 - 9:30 is (540,570)
#   14:00 - 14:30 is (840,870)
# Tuesday: No meetings
# Wednesday: No meetings
# Thursday:
#   9:30 - 10:00 is (570,600)
#   11:30 - 12:00 is (690,720)
#   13:00 - 13:30 is (780,810)
#   16:30 - 17:00 is (990,1020)
nicholas_busy = {
    0: [(540,570), (840,870)],
    1: [],
    2: [],
    3: [(570,600), (690,720), (780,810), (990,1020)]
}

# Virginia's busy schedule:
# Monday:
#   9:00 - 10:30 is (540,630)
#   11:00 - 12:30 is (660,750)
#   14:00 - 16:30 is (840,990)
# Tuesday:
#   9:00 - 11:00 is (540,660)
#   11:30 - 17:00 is (690,1020)
# Wednesday:
#   9:00 - 17:00 is (540,1020)
# Thursday:
#   9:00 - 17:00 is (540,1020)
virginia_busy = {
    0: [(540,630), (660,750), (840,990)],
    1: [(540,660), (690,1020)],
    2: [(540,1020)],
    3: [(540,1020)]
}

# Utility function to enforce that a meeting starting at s (lasting 'duration' minutes)
# does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate through candidate days in preferred order.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes from midnight

    # The meeting must fit within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add busy constraints for Nicholas.
    for (busy_start, busy_end) in nicholas_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add busy constraints for Virginia.
    for (busy_start, busy_end) in virginia_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Now, iterate minute-by-minute over possible start times.
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
    # Convert minutes to HH:MM.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day],
                  start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")