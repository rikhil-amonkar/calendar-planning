from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define the meeting start time (in minutes from midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Brandon prefers not to meet on Tuesday, so try Monday and Wednesday first.
candidate_days = [0, 2, 1]

# Brandon's busy schedule (in minutes):
# Monday: 10:30 to 11:30 -> (630, 690), 12:00 to 12:30 -> (720, 750), 13:30 to 14:30 -> (810, 870)
# Tuesday: 10:00 to 11:30 -> (600, 690), 14:00 to 14:30 -> (840, 870), 15:30 to 16:30 -> (930, 990)
# Wednesday: 12:00 to 13:30 -> (720, 810), 14:00 to 15:00 -> (840, 900)
brandon_busy = {
    0: [(630, 690), (720, 750), (810, 870)],
    1: [(600, 690), (840, 870), (930, 990)],
    2: [(720, 810), (840, 900)]
}

# Olivia's busy schedule (in minutes):
# Monday: 9:00 to 12:00 -> (540, 720), 12:30 to 13:30 -> (750, 810), 14:00 to 17:00 -> (840, 1020)
# Tuesday: 9:00 to 11:00 -> (540, 660), 12:00 to 13:30 -> (720, 810),
#          14:30 to 15:00 -> (870, 900), 15:30 to 16:00 -> (930, 960), 16:30 to 17:00 -> (990, 1020)
# Wednesday: 9:00 to 10:00 -> (540, 600), 10:30 to 11:00 -> (630, 660), 11:30 to 12:00 -> (690, 720),
#            12:30 to 13:30 -> (750, 810), 16:00 to 17:00 -> (960, 1020)
olivia_busy = {
    0: [(540, 720), (750, 810), (840, 1020)],
    1: [(540, 660), (720, 810), (870, 900), (930, 960), (990, 1020)],
    2: [(540, 600), (630, 660), (690, 720), (750, 810), (960, 1020)]
}

# Helper function: meeting interval [start, start+duration) must not overlap a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try candidate days in the defined order
for day in candidate_days:
    solver = Solver()
    # The meeting must lie within work hours: [WORK_START, WORK_END]
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Brandon's busy constraints for the day.
    for b_start, b_end in brandon_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Olivia's busy constraints for the day.
    for b_start, b_end in olivia_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for the earliest start time (minute-by-minute)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # remove the temporary constraint
            break
        solver.pop()
    
    if found:
        break

if found:
    selected_end = selected_start + duration
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[selected_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")