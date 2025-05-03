from z3 import Solver, Int, Or, sat

# Meeting duration (in minutes)
duration = 60

# Meeting start (in minutes after midnight)
start = Int("start")

# Define work hours: 9:00 to 17:00 (in minutes after midnight)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
candidate_days = [0, 1, 2]

# Kathleen's busy schedule (in minutes)
# Monday: 12:30 to 13:30 -> (750, 810)
# Tuesday: 10:30 to 11:00 -> (630, 660), 16:30 to 17:00 -> (990, 1020)
# Wednesday: no meetings
kathleen_busy = {
    0: [(750, 810)],
    1: [(630, 660), (990, 1020)],
    2: []
}

# Albert's busy schedule (in minutes)
# Monday: 9:00 to 17:00 -> (540, 1020)
# Tuesday: 9:30 to 11:00 -> (570, 660), 11:30 to 12:00 -> (690, 720),
#          12:30 to 13:00 -> (750, 780), 13:30 to 14:00 -> (810, 840),
#          14:30 to 15:00 -> (870, 900), 15:30 to 16:30 -> (930, 990)
# Wednesday: 9:00 to 10:00 -> (540, 600), 11:00 to 11:30 -> (660, 690),
#            12:00 to 14:00 -> (720, 840), 15:00 to 15:30 -> (900, 930),
#            16:30 to 17:00 -> (990, 1020)
albert_busy = {
    0: [(540, 1020)],
    1: [(570, 660), (690, 720), (750, 780), (810, 840), (870, 900), (930, 990)],
    2: [(540, 600), (660, 690), (720, 840), (900, 930), (990, 1020)]
}

# Albert cannot meet on Wednesday before 15:00.
# 15:00 is 900 minutes after midnight.

# Helper function to ensure meeting [start, start+duration) does NOT overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None          # Day index on which meeting is scheduled
meeting_start_val = None    # Meeting start time (in minutes)

# Iterate over each candidate day (Monday, Tuesday, Wednesday)
for day in candidate_days:
    solver = Solver()
    # Meeting must be scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Extra constraint for Wednesday: Albert cannot meet before 15:00.
    if day == 2:
        solver.add(start >= 900)
    
    # Add Kathleen's busy constraints for this day.
    for busy_start, busy_end in kathleen_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Albert's busy constraints for this day.
    for busy_start, busy_end in albert_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try every minute within available work hours to find the earliest feasible start time.
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