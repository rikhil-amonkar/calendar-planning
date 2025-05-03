from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define the meeting start time variable in minutes from midnight.
start = Int("start")

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Susan would rather not meet on Tuesday so we'll try Monday and Wednesday first.
# Additionally, Sandra cannot meet on Monday after 16:00, so if the meeting is on Monday, it must finish by 16:00 (i.e. start + duration <= 960).
candidate_days = [0, 2, 1]

# Susan's busy schedule (in minutes):
# Monday: 12:30 to 13:00 -> (750, 780), 13:30 to 14:00 -> (810, 840)
# Tuesday: 11:30 to 12:00 -> (690, 720)
# Wednesday: 9:30 to 10:30 -> (570, 630), 14:00 to 14:30 -> (840, 870), 15:30 to 16:30 -> (930, 990)
susan_busy = {
    0: [(750, 780), (810, 840)],
    1: [(690, 720)],
    2: [(570, 630), (840, 870), (930, 990)]
}

# Sandra's busy schedule (in minutes):
# Monday: 9:00 to 13:00 -> (540, 780), 14:00 to 15:00 -> (840, 900), 16:00 to 16:30 -> (960, 990)
# Tuesday: 9:00 to 9:30 -> (540, 570), 10:30 to 12:00 -> (630, 720), 12:30 to 13:30 -> (750, 810),
#          14:00 to 14:30 -> (840, 870), 16:00 to 17:00 -> (960, 1020)
# Wednesday: 9:00 to 11:30 -> (540, 690), 12:00 to 12:30 -> (720, 750), 13:00 to 17:00 -> (780, 1020)
sandra_busy = {
    0: [(540, 780), (840, 900), (960, 990)],
    1: [(540, 570), (630, 720), (750, 810), (840, 870), (960, 1020)],
    2: [(540, 690), (720, 750), (780, 1020)]
}

# Helper function: returns a constraint that the meeting interval [start, start+duration)
# does not overlap a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try candidate days in the preferred order (Monday, Wednesday, then Tuesday)
for day in candidate_days:
    solver = Solver()
    # Meeting must be within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Additional constraint for Monday: Sandra cannot meet after 16:00.
    if day == 0:
        solver.add(start + duration <= 960)  # meeting must end by 16:00
    
    # Add constraints for Susan's busy times for the day.
    for b_start, b_end in susan_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add constraints for Sandra's busy times for the day.
    for b_start, b_end in sandra_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search minute-by-minute from the start of work hours for the earliest available time slot.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # Remove the temporary constraint
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