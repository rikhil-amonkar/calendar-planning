from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define the meeting start time in minutes from midnight.
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Define days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Austin does not want to meet on Tuesday, so we try Monday and Wednesday first.
candidate_days = [0, 2, 1]

# Austin's busy schedule (in minutes):
# Monday: 10:30 to 11:00 -> (630, 660), 14:30 to 15:00 -> (870, 900), 15:30 to 16:00 -> (930, 960)
# Tuesday: 9:30 to 10:00 -> (570, 600), 12:30 to 13:00 -> (750, 780), 13:30 to 14:00 -> (810, 840), 15:30 to 16:00 -> (930, 960)
# Wednesday: 9:00 to 9:30 -> (540, 570), 10:30 to 11:00 -> (630, 660), 12:00 to 12:30 -> (720, 750),
#            14:00 to 14:30 -> (840, 870), 15:00 to 15:30 -> (900, 930), 16:00 to 17:00 -> (960, 1020)
austin_busy = {
    0: [(630, 660), (870, 900), (930, 960)],
    1: [(570, 600), (750, 780), (810, 840), (930, 960)],
    2: [(540, 570), (630, 660), (720, 750), (840, 870), (900, 930), (960, 1020)]
}

# Madison's busy schedule (in minutes):
# Monday: 9:00 to 12:30 -> (540, 750), 13:30 to 15:30 -> (810, 930), 16:00 to 17:00 -> (960, 1020)
# Tuesday: 9:30 to 11:30 -> (570, 690), 12:00 to 12:30 -> (720, 750), 13:30 to 14:00 -> (810, 840), 16:00 to 17:00 -> (960, 1020)
# Wednesday: 10:30 to 11:00 -> (630, 660), 12:30 to 13:00 -> (750, 780), 13:30 to 15:00 -> (810, 900)
madison_busy = {
    0: [(540, 750), (810, 930), (960, 1020)],
    1: [(570, 690), (720, 750), (810, 840), (960, 1020)],
    2: [(630, 660), (750, 780), (810, 900)]
}

# Helper function: the meeting interval [start, start+duration) must not overlap a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try candidate days in the preferred order: Monday, Wednesday, then Tuesday.
for day in candidate_days:
    solver = Solver()
    
    # Meeting must be completely inside the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add constraints for Austin's busy times on the current day.
    for b_start, b_end in austin_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add constraints for Madison's busy times on the current day.
    for b_start, b_end in madison_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search minute-by-minute from the start of work hours for the earliest valid time slot.
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
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
        day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that meets all constraints.")