from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Workday boundaries: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Stephanie's busy schedule (times in minutes from midnight):
# Monday: 9:30-10:00, 10:30-11:00, 11:30-12:00, 14:00-14:30
# Tuesday: 12:00-13:00
# Wednesday: 9:00-10:00, 13:00-14:00
stephanie_busy = {
    0: [(570,600), (630,660), (690,720), (840,870)],
    1: [(720,780)],
    2: [(540,600), (780,840)]
}

# Betty's busy schedule (times in minutes):
# Monday: 9:00-10:00, 11:00-11:30, 14:30-15:00, 15:30-16:00
# Tuesday: 9:00-9:30, 11:30-12:00, 12:30-14:30, 15:30-16:00
# Wednesday: 10:00-11:30, 12:00-14:00, 14:30-17:00
betty_busy = {
    0: [(540,600), (660,690), (870,900), (930,960)],
    1: [(540,570), (690,720), (750,870), (930,960)],
    2: [(600,690), (720,840), (870,1020)]
}

# Additional constraints:
# 1. Stephanie would like to avoid more meetings on Monday.
#    So we do not schedule on Monday (day 0) if possible.
# 2. Betty cannot meet on Tuesday after 12:30.
#    For Tuesday (day 1), we add the constraint that the meeting must finish by 12:30 (750 minutes).

# Helper function: the meeting interval [start, start+duration) must not overlap with a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
meeting_day = None   # day: 0,1,2
meeting_start = None # meeting start time (in minutes from midnight)

# Try days in the preferred order: since Stephanie prefers to avoid Monday,
# we first try Tuesday, then Wednesday, and use Monday only as fallback.
for day in [1, 2, 0]:
    solver = Solver()
    # Meeting must lie within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Tuesday, enforce that the meeting finishes by 12:30 (750 minutes)
    if day == 1:
        solver.add(start + duration <= 750)
    
    # Avoid Monday if possible (Stephanie's preference)
    if day == 0:
        solver.add(False)
    
    # Add Stephanie's busy constraints for the day.
    for busy_start, busy_end in stephanie_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Betty's busy constraints for the day.
    for busy_start, busy_end in betty_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try possible meeting start times in ascending order to get the earliest available slot.
    lower_bound = WORK_START
    upper_bound = WORK_END - duration
    for t in range(lower_bound, upper_bound + 1):
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
    # Convert minutes to HH:MM format:
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")