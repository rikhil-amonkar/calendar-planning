from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define meeting start time variable in minutes from midnight.
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Define days as integers: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Amy would like to avoid more meetings on Monday.
# So, we consider Tuesday and Wednesday first, then Monday if needed.
candidate_days = [1, 2, 0]

# Amy's busy schedule (times are in minutes from midnight):
# Monday: 11:30-12:30 -> (690,750), 13:30-14:00 -> (810,840), 14:30-15:00 -> (870,900), 16:30-17:00 -> (990,1020)
# Tuesday: 10:30-11:00 -> (630,660), 12:30-13:00 -> (750,780), 13:30-14:00 -> (810,840), 15:30-17:00 -> (930,1020)
# Wednesday: 11:30-12:00 -> (690,720), 15:00-15:30 -> (900,930), 16:00-16:30 -> (960,990)
amy_busy = {
    0: [(690,750), (810,840), (870,900), (990,1020)],
    1: [(630,660), (750,780), (810,840), (930,1020)],
    2: [(690,720), (900,930), (960,990)]
}

# Kevin's busy schedule:
# Monday: 9:00-11:00 -> (540,660), 11:30-17:00 -> (690,1020)
# Tuesday: 9:00-10:30 -> (540,630), 11:00-16:30 -> (660,990)
# Wednesday: 9:00-9:30 -> (540,570), 10:00-17:00 -> (600,1020)
kevin_busy = {
    0: [(540,660), (690,1020)],
    1: [(540,630), (660,990)],
    2: [(540,570), (600,1020)]
}

# Helper function: for a given busy interval [b_start, b_end),
# the meeting time [start, start+duration) must either finish on or before b_start,
# or start on or after b_end, so that it does not overlap.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try each candidate day in our preferred order.
for day in candidate_days:
    solver = Solver()
    # The meeting must be completely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Amy's constraints for the day.
    for b_start, b_end in amy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Kevin's constraints for the day.
    for b_start, b_end in kevin_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search minute by minute within the work hours for the earliest valid meeting start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    if found:
        break

if found:
    selected_end = selected_start + duration
    # Convert minutes into hour:minute format
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that meets all constraints.")