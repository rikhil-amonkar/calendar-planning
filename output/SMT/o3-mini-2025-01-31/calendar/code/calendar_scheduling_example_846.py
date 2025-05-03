from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes).
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Jesse's busy schedule (times in minutes since midnight):
# Monday:   12:00 to 12:30 -> (720,750),    14:30 to 15:30 -> (870,930)
# Tuesday:  free (no busy intervals)
# Wednesday: 13:00 to 13:30 -> (780,810)
# Thursday:  9:30 to 10:00 -> (570,600), 11:00 to 11:30 -> (660,690),
#            12:30 to 13:00 -> (750,780), 14:30 to 15:00 -> (870,900)
jesse_busy = {
    0: [(720,750), (870,930)],
    1: [],  # Tuesday: no busy slots for Jesse
    2: [(780,810)],
    3: [(570,600), (660,690), (750,780), (870,900)]
}

# Raymond's busy schedule:
# Monday:    9:00 to 17:00 -> (540,1020)
# Tuesday:   9:00 to 13:00 -> (540,780),   14:00 to 17:00 -> (840,1020)
# Wednesday: 9:00 to 17:00 -> (540,1020)
# Thursday:  9:00 to 17:00 -> (540,1020)
raymond_busy = {
    0: [(540,1020)],
    1: [(540,780), (840,1020)],
    2: [(540,1020)],
    3: [(540,1020)]
}

# Utility function to ensure that the meeting starting at s (with duration) does NOT overlap a busy interval:
# It either ends before the busy interval starts, or starts after the busy interval ends.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order: Monday, Tuesday, Wednesday, Thursday.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes
    
    # Meeting must be within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add Jesse's busy constraints for the day.
    for (b_start, b_end) in jesse_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add Raymond's busy constraints for the day.
    for (b_start, b_end) in raymond_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Iterate over all possible start times within work hours (in minutes)
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