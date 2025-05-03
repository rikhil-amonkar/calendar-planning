from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting is 30 minutes long
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules for Melissa and Ruth.
# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Melissa's busy schedule (times in minutes from midnight):
# Monday: 9:00-9:30, 10:30-11:30, 13:30-14:00, 14:30-15:00
# Tuesday: 9:00-9:30, 12:00-12:30, 13:30-14:00, 14:30-15:00
# Wednesday: 9:00-10:00, 11:00-11:30, 13:00-14:30, 16:30-17:00
melissa_busy = {
    0: [(540,570), (630,690), (810,840), (870,900)],
    1: [(540,570), (720,750), (810,840), (870,900)],
    2: [(540,600), (660,690), (780,870), (990,1020)]
}

# Ruth's busy schedule (times in minutes from midnight):
# Monday: 9:30-11:00, 12:00-14:30, 15:00-17:00
# Tuesday: 10:00-10:30, 12:00-12:30, 13:30-14:30, 15:00-15:30
# Wednesday: 10:00-10:30, 11:00-11:30, 12:00-13:30, 14:00-14:30, 15:30-17:00
ruth_busy = {
    0: [(570,660), (720,870), (900,1020)],
    1: [(600,630), (720,750), (810,870), (900,930)],
    2: [(600,630), (660,690), (720,810), (840,870), (930,1020)]
}

# Additional constraints:
# Melissa does not want to meet on Tuesday (day 1).
# The meeting may be scheduled on Monday (day 0) or Wednesday (day 2).

# Helper function: the meeting interval [start, start+duration) must not overlap with a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    # Either the meeting ends at or before busy starts, or starts at or after busy ends.
    return Or(start + duration <= b_start, start >= b_end)

found = False
meeting_day = None  # 0: Monday, 1: Tuesday, 2: Wednesday
meeting_start = None

# Consider days in order: Monday, Tuesday, Wednesday.
# Even though Tuesday is an option by the general scheduling, Melissa prefers not to meet then.
for day in [0, 1, 2]:
    solver = Solver()
    
    # Meeting must be within the work day.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Melissa's busy constraints for the day.
    for b_start, b_end in melissa_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Ruth's busy constraints for the day.
    for b_start, b_end in ruth_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Apply additional day-specific preferences.
    if day == 1:
        # Melissa does not want to meet on Tuesday.
        solver.add(False)
    
    # Iterate over the possible start times in ascending order (to get the earliest possibility).
    lower_bound = WORK_START
    upper_bound = WORK_END - duration
    for t in range(lower_bound, upper_bound + 1):
        solver.push()  # Save solver state
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove constraint for t
            break
        solver.pop()  # remove constraint for t
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")