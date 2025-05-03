from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Scott is free all week, so no busy intervals for him.

# Jeffrey's busy schedule (times in minutes):
# Monday (day 0):
#   9:30 to 12:00 => (570, 720)
#   12:30 to 13:00 => (750, 780)
#   14:00 to 14:30 => (840, 870)
#   16:30 to 17:00 => (990, 1020)
#
# Tuesday (day 1):
#   9:30 to 10:30 => (570, 630)
#   11:30 to 12:00 => (690, 720)
#   12:30 to 13:00 => (750, 780)
#   13:30 to 15:30 => (810, 930)
#   16:00 to 16:30 => (960, 990)
#
# Wednesday (day 2):
#   9:00 to 11:30 => (540, 690)
#   12:00 to 17:00 => (720, 1020)
jeffrey_busy = {
    0: [(570, 720), (750, 780), (840, 870), (990, 1020)],
    1: [(570, 630), (690, 720), (750, 780), (810, 930), (960, 990)],
    2: [(540, 690), (720, 1020)]
}

def non_overlap(busy_start, busy_end):
    # Meeting interval [start, start+duration) must not overlap interval [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0=Monday, 1=Tuesday, 2=Wednesday
meeting_start = None

# The group would like to meet at their earliest availability.
# We'll check days in order: Monday, Tuesday, then Wednesday.
for day in [0, 1, 2]:
    solver = Solver()
    # Restrict meeting within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Jeffrey's constraints for this day.
    for busy_start, busy_end in jeffrey_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try potential start times from 9:00 (540) to latest start which is (1020 - duration)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")