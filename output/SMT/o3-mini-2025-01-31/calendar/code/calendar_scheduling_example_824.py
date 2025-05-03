from z3 import Solver, Int, Or, sat

# Meeting duration is 60 minutes.
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60     # 540
WORK_END = 17 * 60     # 1020

# Represent days as:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Kimberly has no busy intervals.
kimberly_busy = {
    0: [],
    1: [],
    2: [],
    3: []
}

# Timothy's busy intervals (in minutes since midnight):
# Monday:
#   9:00-9:30 -> (540,570)
#   10:00-11:30 -> (600,690)
#   12:30-13:30 -> (750,810)
#   15:00-15:30 -> (900,930)
#   16:00-17:00 -> (960,1020)
# Tuesday:
#   9:30-10:30 -> (570,630)
#   11:30-13:00 -> (690,780)
#   13:30-14:30 -> (810,870)
#   15:30-16:00 -> (930,960)
# Wednesday:
#   9:00-9:30 -> (540,570)
#   10:00-11:00 -> (600,660)
#   11:30-16:00 -> (690,960)
#   16:30-17:00 -> (990,1020)
# Thursday:
#   9:00-17:00 -> (540,1020)
timothy_busy = {
    0: [(540,570), (600,690), (750,810), (900,930), (960,1020)],
    1: [(570,630), (690,780), (810,870), (930,960)],
    2: [(540,570), (600,660), (690,960), (990,1020)],
    3: [(540,1020)]  # Timothy is busy the entire day on Thursday.
}

solution_found = False
selected_day = None
selected_start = None

# Helper function to generate a constraint that a meeting starting at start_var
# of duration 'duration' does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Preferences:
# 1. Kimberly would like to avoid more meetings on Monday after 13:30.
#    For a meeting on Monday (day==0) the meeting must end by 13:30 (810),
#    i.e. start + 60 <= 810.
# 2. Kimberly would also like to avoid meetings on Tuesday.
#
# The meeting should be scheduled at the earliest possible day and time.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # Constrain the meeting to lie fully within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Kimberly's preferences:
    # Disallow Tuesday entirely.
    if day == 1:
        solver.add(False)
    
    # On Monday, disallow meetings that extend beyond 13:30.
    if day == 0:
        solver.add(start + duration <= 13 * 60 + 30)  # i.e., start + 60 <= 810
    
    # Kimberly has no busy intervals. (No constraints to add.)
    
    # Add constraints for Timothy's busy intervals.
    for (busy_start, busy_end) in timothy_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search through each possible start time (minute-by-minute) for the day.
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
    # Convert minutes to hour and minute format.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")