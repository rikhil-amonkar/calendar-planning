from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours in minutes: from 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Busy schedules in minutes

# James's busy schedule:
# Monday: 9:30-11:30 -> (570, 690), 12:00-12:30 -> (720, 750),
#         13:00-14:00 -> (780, 840), 14:30-15:00 -> (870, 900),
#         16:00-16:30 -> (960, 990)
# Tuesday: 10:00-10:30 -> (600, 630), 12:00-13:00 -> (720, 780),
#          14:00-14:30 -> (840, 870), 15:00-15:30 -> (900, 930),
#          16:00-16:30 -> (960, 990)
# Wednesday: 9:30-10:30 -> (570, 630), 12:00-12:30 -> (720, 750),
#            13:30-14:00 -> (810, 840), 14:30-15:00 -> (870, 900)
james_busy = {
    0: [(570, 690), (720, 750), (780, 840), (870, 900), (960, 990)],
    1: [(600, 630), (720, 780), (840, 870), (900, 930), (960, 990)],
    2: [(570, 630), (720, 750), (810, 840), (870, 900)]
}

# Diane's busy schedule:
# Monday: 10:00-11:00 -> (600, 660), 11:30-12:00 -> (690, 720),
#         13:00-13:30 -> (780, 810), 14:00-16:30 -> (840, 990)
# Tuesday: 10:30-11:00 -> (630, 660), 11:30-13:00 -> (690, 780),
#          13:30-14:00 -> (810, 840), 14:30-15:00 -> (870, 900),
#          15:30-16:00 -> (930, 960)
# Wednesday: 9:00-10:30 -> (540, 630), 11:00-11:30 -> (660, 690),
#            12:00-15:00 -> (720, 900), 15:30-16:30 -> (930, 990)
diane_busy = {
    0: [(600, 660), (690, 720), (780, 810), (840, 990)],
    1: [(630, 660), (690, 780), (810, 840), (870, 900), (930, 960)],
    2: [(540, 630), (660, 690), (720, 900), (930, 990)]
}

# Define a helper function that ensures the meeting [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # chosen day (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

# Iterate over candidate days in order (Monday, then Tuesday, then Wednesday)
for day in candidate_days:
    solver = Solver()
    # Enforce the meeting to occur within working hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add James's busy constraints for the current day
    for b_start, b_end in james_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Diane's busy constraints for the current day
    for b_start, b_end in diane_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Look for the earliest feasible start time on this day.
    # The meeting must start between WORK_START and WORK_END - duration.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")