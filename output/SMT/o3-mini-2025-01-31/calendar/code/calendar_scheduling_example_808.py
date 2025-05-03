from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours in minutes (from midnight): 9:00 is 540, 17:00 is 1020.
WORK_START = 9 * 60   # 540
WORK_END   = 17 * 60  # 1020

# Days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedules for Michelle (in minutes since midnight):
# Monday: 13:30-14:00  => (810,840), 14:30-15:00 => (870,900)
# Tuesday: 10:30-12:00 => (630,720), 12:30-13:00 => (750,780), 14:30-15:30 => (870,930), 16:30-17:00 => (990,1020)
# Wednesday: 9:30-10:00 => (570,600), 14:00-14:30 => (840,870), 16:00-16:30 => (960,990)
# Thursday: 10:00-10:30 => (600,630), 11:00-12:00 => (660,720),
#           13:00-13:30 => (780,810), 15:00-15:30 => (900,930), 16:30-17:00 => (990,1020)
michelle_busy = {
    0: [(810, 840), (870, 900)],
    1: [(630, 720), (750, 780), (870, 930), (990, 1020)],
    2: [(570, 600), (840, 870), (960, 990)],
    3: [(600, 630), (660, 720), (780, 810), (900, 930), (990, 1020)]
}

# Busy schedules for Laura (in minutes since midnight):
# Monday: 9:30-10:00 => (570,600), 10:30-13:00 => (630,780), 14:30-15:30 => (870,930), 16:00-16:30 => (960,990)
# Tuesday: 9:00-10:30  => (540,630), 11:00-12:00 => (660,720), 12:30-14:30 => (750,870), 15:30-17:00 => (930,1020)
# Wednesday: 9:00-11:30 => (540,690), 12:00-13:30 => (720,810), 14:30-15:30 => (870,930), 16:00-17:00 => (960,1020)
# Thursday: 9:00-12:30 => (540,750), 13:00-17:00 => (780,1020)
laura_busy = {
    0: [(570, 600), (630, 780), (870, 930), (960, 990)],
    1: [(540, 630), (660, 720), (750, 870), (930, 1020)],
    2: [(540, 690), (720, 810), (870, 930), (960, 1020)],
    3: [(540, 750), (780, 1020)]
}

# Preference constraints:
# Michelle would like to avoid meetings on Tuesday and Thursday.
# Laura does not want to meet on Wednesday, and if meeting on Monday it must finish by 14:30.
#
# We interpret these as hard constraints:
# - If the meeting is on Tuesday (day == 1) or Thursday (day == 3), then disallow.
# - If the meeting is on Wednesday (day == 2), then disallow.
# - If the meeting is on Monday (day == 0), then meeting must finish by 14:30 (i.e. start + duration <= 14:30).
#   Note: 14:30 is 14*60 + 30 = 870 minutes.

# Helper function: ensure that the meeting scheduled at 'start_var' (lasting duration minutes)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate through candidate days in order: Monday (0), Tuesday (1), Wednesday (2), Thursday (3).
# But the preference constraints will effectively filter out Tuesday, Wednesday, and Thursday.
for day in candidate_days:
    solver = Solver()
    
    # Define the meeting start time (in minutes from midnight) for this day.
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply preference constraints:
    # Michelle does not want Tuesday (1) or Thursday (3)
    if day == 1 or day == 3:
        solver.add(False)  # disallow this day

    # Laura does not want to meet on Wednesday (2)
    if day == 2:
        solver.add(False)  # disallow Wednesday

    # If the meeting is on Monday, Laura prefers it finish by 14:30.
    if day == 0:
        solver.add(start + duration <= 870)  # Meeting must end by 14:30.
    
    # Add Michelle's busy time constraints for the day.
    for interval in michelle_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    # Add Laura's busy time constraints for the day.
    for interval in laura_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    # Search for the earliest meeting time on this day by iterating minute by minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        # For Monday, also ensure meeting finishes by 14:30.
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