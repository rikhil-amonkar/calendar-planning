from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time (minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Ryan cannot meet on Wednesday, so only Monday and Tuesday are considered.
# Adam would like to avoid meetings on Monday before 14:30 (i.e., before 14*60+30 = 870 minutes).
#
# We treat the "avoid" as a preference: First try Tuesday.
# If Tuesday yields no solution, then try Monday with an extra constraint that the meeting start is at or after 14:30.

# Ryan's busy schedule (times given in minutes from midnight):
# Monday: 9:30-10:00, 11:00-12:00, 13:00-13:30, 15:30-16:00
# Tuesday: 11:30-12:30, 15:30-16:00
ryan_busy = {
    0: [(570, 600),    # 9:30 to 10:00
        (660, 720),    # 11:00 to 12:00
        (780, 810),    # 13:00 to 13:30
        (930, 960)],   # 15:30 to 16:00
    1: [(690, 750),    # Tuesday: 11:30 to 12:30
        (930, 960)]    # Tuesday: 15:30 to 16:00
}

# Adam's busy schedule:
# Monday: 9:00-10:30, 11:00-13:30, 14:00-16:00, 16:30-17:00
# Tuesday: 9:00-10:00, 10:30-15:30, 16:00-17:00
adam_busy = {
    0: [(540, 630),    # Monday: 9:00 to 10:30
        (660, 810),    # Monday: 11:00 to 13:30
        (840, 960),    # Monday: 14:00 to 16:00
        (990, 1020)],  # Monday: 16:30 to 17:00
    1: [(540, 600),    # Tuesday: 9:00 to 10:00
        (630, 930),    # Tuesday: 10:30 to 15:30
        (960, 1020)]   # Tuesday: 16:00 to 17:00
}

def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration) must not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 = Monday, 1 = Tuesday
meeting_start = None

# Define prioritized day order. 
# Since Ryan cannot meet on Wednesday, and Adam prefers to avoid Monday before 14:30,
# we try Tuesday first.
prioritized_days = [1, 0]

for day in prioritized_days:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If the day is Monday (0) then add Adam's preference: avoid morning meetings.
    # We enforce meeting start must be at or after 14:30 (870 minutes) only when selecting Monday.
    if day == 0:
        solver.add(start >= 870)
    
    # Add Ryan's busy constraints.
    for b_start, b_end in ryan_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Adam's busy constraints.
    for b_start, b_end in adam_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible meeting start times in ascending order.
    # This will result in the earliest available slot for the day.
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
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = {0: "Monday", 1: "Tuesday"}[meeting_day]
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")