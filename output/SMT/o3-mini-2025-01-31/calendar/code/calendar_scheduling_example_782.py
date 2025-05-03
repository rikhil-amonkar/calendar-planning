from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Define meeting start time variable (in minutes from midnight).
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Define days as: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Deborah would rather not meet on Monday or Wednesday.
# Thus, we try Tuesday first and then fall back to Monday and Wednesday if needed.
candidate_days = [1, 0, 2]

# Denise's busy schedule (times in minutes):
# Monday: 13:00-13:30 -> (780,810), 15:00-15:30 -> (900,930)
# Tuesday: 10:00-10:30 -> (600,630)
# Wednesday: 11:30-12:00 -> (690,720)
denise_busy = {
    0: [(780, 810), (900, 930)],
    1: [(600, 630)],
    2: [(690, 720)]
}

# Deborah's busy schedule (times in minutes):
# Monday: 9:00-9:30 -> (540,570), 10:30-12:00 -> (630,720), 12:30-15:00 -> (750,900)
# Tuesday: 9:00-13:30 -> (540,810), 14:30-17:00 -> (870,1020)
# Wednesday: 9:00-10:00 -> (540,600), 11:30-12:00 -> (690,720),
#            12:30-13:30 -> (750,810), 14:30-15:00 -> (870,900), 15:30-16:00 -> (930,960)
deborah_busy = {
    0: [(540,570), (630,720), (750,900)],
    1: [(540,810), (870,1020)],
    2: [(540,600), (690,720), (750,810), (870,900), (930,960)]
}

# Helper function: the meeting interval [start, start+duration) must not overlap a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try candidate days in the preferred order.
for day in candidate_days:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Denise's busy constraints for the day.
    for b_start, b_end in denise_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Deborah's busy constraints for the day.
    for b_start, b_end in deborah_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search minute-by-minute from the start of work hours for the earliest valid meeting time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # remove temporary constraint before breaking out
            break
        solver.pop()
    
    if found:
        break

if found:
    selected_end = selected_start + duration
    # Convert minutes to hour:minute format
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that meets all constraints.")