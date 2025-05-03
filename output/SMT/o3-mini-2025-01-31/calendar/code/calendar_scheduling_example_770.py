from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# The meeting start time (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Arthur's busy schedule (times in minutes):
# Monday: 9:30-10:00 -> (570,600), 10:30-11:30 -> (630,690), 13:00-14:00 -> (780,840)
# Tuesday: 9:00-12:30 -> (540,750), 13:00-14:00 -> (780,840), 15:30-17:00 -> (930,1020)
# Wednesday: 10:00-10:30 -> (600,630), 11:30-12:00 -> (690,720), 14:00-14:30 -> (840,870)
arthur_busy = {
    0: [(570, 600), (630, 690), (780, 840)],
    1: [(540, 750), (780, 840), (930, 1020)],
    2: [(600, 630), (690, 720), (840, 870)]
}

# Eric's busy schedule (times in minutes):
# Monday: 9:00-9:30 -> (540,570), 10:00-13:00 -> (600,780), 13:30-14:00 -> (810,840), 15:00-17:00 -> (900,1020)
# Tuesday: 9:30-10:00 -> (570,600), 10:30-12:30 -> (630,750), 13:00-15:30 -> (780,930), 16:30-17:00 -> (990,1020)
# Wednesday: 9:30-11:00 -> (570,660), 11:30-16:30 -> (690,990)
eric_busy = {
    0: [(540, 570), (600, 780), (810, 840), (900, 1020)],
    1: [(570, 600), (630, 750), (780, 930), (990, 1020)],
    2: [(570, 660), (690, 990)]
}

def non_overlap(busy_start, busy_end):
    """
    The meeting interval [start, start+duration) must not overlap
    with a busy interval [busy_start, busy_end).
    """
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None
meeting_start_val = None

# Try candidate days in order: Monday, Tuesday, Wednesday.
for day in candidate_days:
    solver = Solver()
    
    # The meeting must be completely inside working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Arthur's busy constraints for the given day.
    for b_start, b_end in arthur_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Eric's busy constraints for the given day.
    for b_start, b_end in eric_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for the earliest valid start time (minute-by-minute search).
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
    start_hr, start_min = divmod(meeting_start_val, 60)
    end_hr, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")