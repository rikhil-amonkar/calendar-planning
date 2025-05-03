from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # length of meeting in minutes (1 hour)
start = Int("start")  # meeting start time (in minutes from midnight)

# Work day limits: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Natalie’s busy schedule:
# Monday: 16:00-16:30 -> (960, 990)
# Tuesday: 9:00-9:30 -> (540,570), 10:00-12:00 -> (600,720),
#          12:30-13:00 -> (750,780), 15:00-15:30 -> (900,930)
natalie_busy = {
    0: [(960, 990)],
    1: [(540, 570), (600, 720), (750, 780), (900, 930)]
}

# Frances’s busy schedule:
# Monday: 9:00-10:30 -> (540,630), 11:00-11:30 -> (660,690),
#         13:00-13:30 -> (780,810), 14:30-17:00 -> (870,1020)
# Tuesday: 9:00-10:00 -> (540,600), 12:00-13:00 -> (720,780),
#          13:30-14:00 -> (810,840), 14:30-16:00 -> (870,960)
frances_busy = {
    0: [(540, 630), (660, 690), (780, 810), (870, 1020)],
    1: [(540, 600), (720, 780), (810, 840), (870, 960)]
}

# Additional preferences:
# - Natalie would like to avoid more meetings on Tuesday.
#   (We incorporate this by trying Monday first.)
# - Frances does not want to meet on Monday after 13:30.
#   (Thus, for Monday, enforce meeting must end by 13:30 (810 minutes).)

# A helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try days in order: Monday (0) then Tuesday (1).
for day_val in [0, 1]:
    solver = Solver()
    
    # Meeting must be within the work day.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Natalie.
    for (busy_start, busy_end) in natalie_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy constraints for Frances.
    for (busy_start, busy_end) in frances_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add additional constraint for Monday: Frances does not want meetings after 13:30.
    if day_val == 0:
        solver.add(start + duration <= 13 * 60 + 30)  # meeting ends by 13:30 (810 minutes)
    
    # Try possible start times minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day_val
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")