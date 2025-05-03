from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Samantha's busy schedule (in minutes from midnight)
# Monday is day 0, Tuesday is day 1.
# Monday busy intervals:
#   10:00 to 10:30 -> (600, 630)
#   13:00 to 15:30 -> (780, 930)
# Tuesday busy intervals:
#   9:00 to 11:00   -> (540, 660)
#   12:00 to 12:30  -> (720, 750)
#   13:00 to 13:30  -> (780, 810)
#   14:00 to 14:30  -> (840, 870)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 17:00  -> (960, 1020)
samantha_busy = {
    0: [(600, 630), (780, 930)],
    1: [(540, 660), (720, 750), (780, 810), (840, 870), (900, 930), (960, 1020)]
}

# Peter has no meetings scheduled, so no busy intervals to consider for him.

# Samantha's preference is to avoid more meetings on Monday before 15:00.
# We interpret this as: if scheduling on Monday (day 0), the meeting's start time
# must be at or after 15:00 (i.e., 900 minutes). (Note: given her Monday busy until 15:30,
# only meetings starting at 930 will actually fit, but the constraint is stated as before 15:00.)
def add_preference_constraints(solver, day):
    if day == 0:  # Monday
        solver.add(start >= 900)

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Because Samantha prefers to avoid Monday before 15:00, we try Tuesday first.
for day in [1, 0]:
    solver = Solver()
    
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy time constraints for Samantha for the day.
    for b_start, b_end in samantha_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Samantha's preference constraint if it is Monday.
    add_preference_constraints(solver, day)
    
    # Iterate over possible start times from WORK_START in ascending order.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary assignment
            break
        solver.pop()
        
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")