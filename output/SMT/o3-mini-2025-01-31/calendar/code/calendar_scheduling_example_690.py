from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration is 1 hour: 60 minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Doris's busy schedule:
# Monday:
#   10:30 to 11:00 -> (630, 660)
#   12:30 to 13:00 -> (750, 780)
#   14:00 to 14:30 -> (840, 870)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   11:00 to 11:30 -> (660, 690)
#   16:30 to 17:00 -> (990, 1020)
doris_busy = {
    0: [(630, 660), (750, 780), (840, 870), (990, 1020)],
    1: [(660, 690), (990, 1020)]
}

# Carol's busy schedule:
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:30 -> (690, 750)
#   13:30 to 14:30 -> (810, 870)
#   15:30 to 16:30 -> (930, 990)
# Tuesday:
#   9:00 to 10:00 -> (540, 600)
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 15:00 -> (840, 900)
#   15:30 to 16:30 -> (930, 990)
carol_busy = {
    0: [(600, 630), (690, 750), (810, 870), (930, 990)],
    1: [(540, 600), (660, 690), (720, 750), (780, 810), (840, 900), (930, 990)]
}

# Helper function: given a busy interval [busy_start, busy_end),
# returns a Z3 constraint ensuring that the meeting [start, start+duration) does NOT overlap with it.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We want to schedule at the earliest availability: try Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    # The meeting must fit within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Doris's busy intervals for the current day.
    for b_start, b_end in doris_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Carol's busy intervals for the current day.
    for b_start, b_end in carol_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Enumerate possible start times in minute increments from WORK_START (earlier times first)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the constraint for t used for this candidate
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format for easier reading.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")