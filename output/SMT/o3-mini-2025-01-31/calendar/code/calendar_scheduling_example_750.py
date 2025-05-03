from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# According to the constraints:
# - Mark would like to avoid meetings on Monday and Wednesday.
# - Timothy does not want to meet on Tuesday before 11:00.
# This leaves Tuesday (day 1) as the only candidate.
candidate_days = [1]

# Busy schedules in minutes
# Timothy's busy schedule:
# Monday: 15:30 to 16:00  => (930, 960)
# Tuesday: 14:30 to 15:30  => (870, 930)
# Wednesday: 10:00 to 11:00 => (600, 660)
#            12:30 to 13:00 => (750, 780)
#            14:30 to 15:00 => (870, 900)
#            16:00 to 16:30 => (960, 990)
timothy_busy = {
    0: [(930, 960)],
    1: [(870, 930)],
    2: [(600, 660), (750, 780), (870, 900), (960, 990)]
}

# Mark's busy schedule:
# Monday: 9:00 to 9:30   => (540, 570)
#         10:30 to 14:00 => (630, 840)
#         14:30 to 15:00 => (870, 900)
#         16:30 to 17:00 => (990, 1020)
# Tuesday: 9:00 to 10:30 => (540, 630)
#          11:00 to 12:00=> (660, 720)
#          12:30 to 17:00=> (750, 1020)
# Wednesday: 9:00 to 12:30=> (540, 750)
#            13:00 to 13:30=> (780, 810)
#            14:00 to 16:00=> (840, 960)
mark_busy = {
    0: [(540, 570), (630, 840), (870, 900), (990, 1020)],
    1: [(540, 630), (660, 720), (750, 1020)],
    2: [(540, 750), (780, 810), (840, 960)]
}

# Tuesday specific preference: Timothy does not want meetings before 11:00.
# 11:00 in minutes is 660.
TUESDAY_MIN_START = 660

# Helper function to ensure that the meeting does not overlap a busy interval.
def non_overlap(busy_start, busy_end):
    # Meeting [start, start+duration) does not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Will hold the chosen day (1 for Tuesday)
meeting_start_val = None # Meeting start time in minutes after midnight (integer)

# Iterate over the candidate days (only Tuesday in this case).
for day in candidate_days:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Tuesday, enforce that the meeting does not start before 11:00.
    if day == 1:
        solver.add(start >= TUESDAY_MIN_START)
    
    # Add Timothy's busy constraints for the current day.
    for busy_start, busy_end in timothy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Mark's busy constraints for the current day.
    for busy_start, busy_end in mark_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Find the earliest meeting time by checking minute-by-minute.
    # Since the meeting must start no earlier than max(WORK_START, TUESDAY_MIN_START) on Tuesday, 
    # we iterate from that time.
    start_iter = max(WORK_START, TUESDAY_MIN_START)
    for t in range(start_iter, WORK_END - duration + 1):
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