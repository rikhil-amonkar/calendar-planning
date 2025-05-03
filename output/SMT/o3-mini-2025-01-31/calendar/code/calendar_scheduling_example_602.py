from z3 import Solver, Int, Or, sat

# Meeting parameters.
duration = 30  # duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day of the meeting: 0 for Monday, 1 for Tuesday

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020
# So the meeting must finish by WORK_END.
# Thus, start + duration <= WORK_END.
    
# Helper function to add non-overlapping (busy) constraints.
def add_busy_intervals(solver, intervals):
    for b_start, b_end in intervals:
        # Meeting interval [start, start+duration) must not overlap the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Busy intervals for Anna:
# Monday: 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:00-13:30, 14:00-15:00, 15:30-16:30
anna_monday_busy = [
    (540, 570),
    (600, 690),
    (720, 750),
    (780, 810),
    (840, 900),
    (930, 990)
]
# Tuesday: 9:00-9:30, 10:00-10:30, 12:00-12:30, 14:30-15:00
anna_tuesday_busy = [
    (540, 570),
    (600, 630),
    (720, 750),
    (870, 900)
]

# Busy intervals for Cheryl:
# Monday: 9:00-12:30, 13:00-16:30
cheryl_monday_busy = [
    (540, 750),
    (780, 990)
]
# Tuesday: 9:00-10:00, 11:00-13:00, 13:30-15:30, 16:00-17:00
cheryl_tuesday_busy = [
    (540, 600),
    (660, 780),
    (810, 930),
    (960, 1020)
]

# We'll try to schedule the meeting on Tuesday first to honor Cheryl's preference
def find_meeting_for_day(target_day, busy_intervals_list):
    solver = Solver()
    # Set work hour constraints.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    # Set day.
    solver.add(day == target_day)
    # Add all busy interval constraints provided in busy_intervals_list.
    for intervals in busy_intervals_list:
        add_busy_intervals(solver, intervals)
    # Search for the earliest meeting start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            model = solver.model()
            meeting_start = model[start].as_long()
            meeting_end = meeting_start + duration
            return meeting_start, meeting_end
        solver.pop()
    return None

# Try Tuesday (target_day = 1) first.
# Gather Tuesday busy intervals for both participants.
tuesday_busy = [anna_tuesday_busy, cheryl_tuesday_busy]
result = find_meeting_for_day(1, tuesday_busy)

if result is not None:
    meeting_day = "Tuesday"
else:
    # If no solution is found on Tuesday, try Monday.
    monday_busy = [anna_monday_busy, cheryl_monday_busy]
    res = find_meeting_for_day(0, monday_busy)
    if res is not None:
        meeting_day = "Monday"
        result = res

if result is not None:
    meeting_start, meeting_end = result
    # Convert meeting times to HH:MM format.
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    print(f"A valid meeting time is on {meeting_day} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")