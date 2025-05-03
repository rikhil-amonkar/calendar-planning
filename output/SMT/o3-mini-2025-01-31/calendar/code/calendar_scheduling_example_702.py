from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Workday boundaries: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# We represent days as: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Robert's busy schedule (times in minutes from midnight):
# Monday (day 0): 11:00-11:30, 14:00-14:30, 15:30-16:00
# Tuesday (day 1): 10:30-11:00, 15:00-15:30
# Wednesday (day 2): 10:00-11:00, 11:30-12:00, 12:30-13:00, 13:30-14:00, 15:00-15:30, 16:00-16:30
robert_busy = {
    0: [(660,690), (840,870), (930,960)],
    1: [(630,660), (900,930)],
    2: [(600,660), (690,720), (750,780), (810,840), (900,930), (960,990)]
}

# Ralph's busy schedule:
# Monday (day 0): 10:00-13:30, 14:00-14:30, 15:00-17:00
# Tuesday (day 1): 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:00-13:00, 14:00-15:30, 16:00-17:00
# Wednesday (day 2): 10:30-11:00, 11:30-12:00, 13:00-14:30, 16:30-17:00
ralph_busy = {
    0: [(600,810), (840,870), (900,1020)],
    1: [(540,570), (600,630), (660,690), (720,780), (840,930), (960,1020)],
    2: [(630,660), (690,720), (780,870), (990,1020)]
}

# Additional constraint:
# Robert would like to avoid more meetings on Monday.
# We incorporate this as a hard constraint and disallow Monday.
# Also, we want to schedule the meeting at the earliest availability (lowest start time).

# Helper function: the meeting interval [start, start+duration) must not overlap with a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
meeting_day = None   # Day chosen: 0 = Monday, 1 = Tuesday, 2 = Wednesday
meeting_start = None  # Meeting start time in minutes

# Since Robert wants to avoid Monday, we try Tuesday and Wednesday first.
# We try days in the order: Tuesday (1), Wednesday (2), then Monday (0) as a fallback.
for day in [1, 2, 0]:
    solver = Solver()
    # The meeting must be within the workday.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If the day is Monday (0) then disallow it.
    if day == 0:
        solver.add(False)
    
    # Add Robert's busy constraints for the day.
    for busy_start, busy_end in robert_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Ralph's busy constraints for the day.
    for busy_start, busy_end in ralph_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # We try possible start times in ascending order to ensure the earliest possible meeting.
    lower_bound = WORK_START
    upper_bound = WORK_END - duration
    for t in range(lower_bound, upper_bound + 1):
        solver.push()  # Save the current state
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the last added constraint for t
            break
        solver.pop()  # Revert and try next time
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