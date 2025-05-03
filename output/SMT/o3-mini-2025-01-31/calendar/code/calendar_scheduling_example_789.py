from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (half an hour)
duration = 30

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540
WORK_END = 17 * 60    # 1020

# Create a Z3 integer variable for the meeting start time (in minutes from midnight)
start = Int("start")

# Encode days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Brenda's busy times (in minutes from midnight)
# Monday: 9:30-10:00 -> (570, 600)
# Tuesday: 9:00-9:30 -> (540, 570), 12:30-13:00 -> (750, 780)
# Wednesday: 9:00-9:30 -> (540,570), 11:00-11:30 -> (660,690),
#            12:30-13:00 -> (750,780), 15:30-16:30 -> (930,990)
brenda_busy = {
    0: [(570, 600)],
    1: [(540, 570), (750, 780)],
    2: [(540, 570), (660, 690), (750, 780), (930, 990)]
}

# Bruce's busy times (in minutes from midnight)
# Monday: 10:00-10:30 -> (600,630), 11:00-11:30 -> (660,690),
#         13:00-15:00 -> (780,900), 15:30-16:30 -> (930,990)
# Tuesday: 9:00-17:00 -> (540,1020)
# Wednesday: 9:00-17:00 -> (540,1020)
bruce_busy = {
    0: [(600, 630), (660, 690), (780, 900), (930, 990)],
    1: [(540, 1020)],
    2: [(540, 1020)]
}

# Bruce's preference: on Monday ("day 0"), he would rather not have meetings after 13:30.
# We encode this as: if the meeting is scheduled on Monday, its start time must be no later than 13:30.
# Note: 13:30 in minutes is 13*60 + 30 = 810.
def bruce_monday_preference(day):
    if day == 0:
        return start <= 810
    return True  # No constraint on other days.

# Helper function: For a busy interval (b_start, b_end) the meeting interval [start, start+duration)
# must not overlap this busy interval.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# We iterate over candidate days in order: Monday (0), then Tuesday (1), then Wednesday (2)
for day in candidate_days:
    solver = Solver()
    
    # Constraint: meeting must be within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Bruce's Monday preference if applicable.
    solver.add(bruce_monday_preference(day))
    
    # Add Brenda's busy constraints for the day.
    for (b_start, b_end) in brenda_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Bruce's busy constraints for the day.
    for (b_start, b_end) in bruce_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))

    # We now iterate minute-by-minute for the earliest available time on this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes into HH:MM format.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")