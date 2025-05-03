from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# For Monday:
# Michelle: 15:30 to 16:30 -> (930, 990)
# Amber: 10:00 to 12:30 -> (600, 750)
#        13:00 to 13:30 -> (780, 810)
#        15:00 to 15:30 -> (900, 930)
#        16:30 to 17:00 -> (990, 1020)
monday_busy = {
    "Michelle": [(930, 990)],
    "Amber": [(600, 750), (780, 810), (900, 930), (990, 1020)]
}

# For Tuesday:
# Michelle: 12:30 to 13:30 -> (750, 810)
# Amber: 9:00 to 10:30 -> (540, 630)
#        12:30 to 15:00 -> (750, 900)
tuesday_busy = {
    "Michelle": [(750, 810)],
    "Amber": [(540, 630), (750, 900)]
}

# Helper function: returns the non-overlap constraint between the meeting [start, start+duration)
# and a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# We want the earliest available time overall.
# We'll first prefer Monday (day=0), then Tuesday (day=1) if Monday has no valid slot.
found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll iterate day by day, checking minute-by-minute for the earliest meeting start.
for d in [0, 1]:  # 0: Monday, 1: Tuesday
    solver = Solver()
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Choose the busy schedule based on the day.
    busy = monday_busy if d == 0 else tuesday_busy
    
    # Add non-overlap constraints for each participant's busy intervals.
    for person in busy:
        for interval in busy[person]:
            solver.add(non_overlap(interval[0], interval[1]))
    
    # Iterate over potential start times (minute-by-minute) within work hours.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = d
            found = True
            solver.pop()
            break
        solver.pop()
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    s_hour, s_min = divmod(meeting_start, 60)
    e_hour, e_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")