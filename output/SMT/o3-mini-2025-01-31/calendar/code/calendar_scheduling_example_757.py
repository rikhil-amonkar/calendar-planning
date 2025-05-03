from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# The meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Justin would rather not meet on Monday, so we consider Tuesday and Wednesday.
candidate_days = [1, 2]

# Noah's busy schedule (in minutes)
# Monday: 9:30-10:00 -> (570,600), 15:00-15:30 -> (900,930), 16:00-16:30 -> (960,990)
# Tuesday: 9:30-10:30 -> (570,630), 16:00-16:30 -> (960,990)
# Wednesday: 9:00-9:30 -> (540,570), 12:00-12:30 -> (720,750)
noah_busy = {
    0: [(570, 600), (900, 930), (960, 990)],
    1: [(570, 630), (960, 990)],
    2: [(540, 570), (720, 750)]
}

# Justin's busy schedule (in minutes)
# Monday: 9:30-11:30 -> (570,690), 12:30-13:30 -> (750,810), 
#         15:00-16:00 -> (900,960), 16:30-17:00 -> (990,1020)
# Tuesday: 9:00-13:30 -> (540,810), 14:00-17:00 -> (840,1020)
# Wednesday: 10:00-11:00 -> (600,660), 12:00-14:30 -> (720,870), 15:00-15:30 -> (900,930)
justin_busy = {
    0: [(570, 690), (750, 810), (900, 960), (990, 1020)],
    1: [(540, 810), (840, 1020)],
    2: [(600, 660), (720, 870), (900, 930)]
}

# Helper function to ensure that the meeting [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day index (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

for day in candidate_days:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Day-specific constraint:
    # Noah would like to avoid meetings on Wednesday after 13:00.
    # If the meeting is on Wednesday (day == 2), ensure that meeting ends by 13:00 (780 minutes).
    if day == 2:
        solver.add(start + duration <= 780)
    
    # Add Noah's busy constraints for this day.
    for b_start, b_end in noah_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Justin's busy constraints for this day.
    for b_start, b_end in justin_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Check for an earliest valid start time on this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop() # Remove temporary assignment
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