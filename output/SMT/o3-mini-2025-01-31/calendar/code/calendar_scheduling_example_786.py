from z3 import Solver, Int, Or, sat

# Meeting duration in minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Create an integer variable to represent the meeting start time (in minutes from midnight)
start = Int("start")

# Days are encoded as: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Pamela would like to avoid meetings on Monday and Tuesday, and on Wednesday she prefers meetings not before 16:00.
# Thus we prioritize Wednesday (with a constraint that start >= 16:00) over the other days.
candidate_days = [2, 0, 1]

# Amy's busy schedule (only specified for Wednesday):
# Wednesday:
#   11:00 to 11:30 -> (660, 690)
#   13:30 to 14:00 -> (810, 840)
amy_busy = {
    2: [(660, 690), (810, 840)]
}

# Pamela's busy schedule:
# Monday:
#   9:00 to 10:30 -> (540, 630)
#   11:00 to 16:30 -> (660, 990)
# Tuesday:
#   9:00 to 9:30  -> (540, 570)
#   10:00 to 17:00 -> (600, 1020)
# Wednesday:
#   9:00 to 9:30  -> (540, 570)
#   10:00 to 11:00 -> (600, 660)
#   11:30 to 13:30 -> (690, 810)
#   14:30 to 15:00 -> (870, 900)
#   16:00 to 16:30 -> (960, 990)
pamela_busy = {
    0: [(540, 630), (660, 990)],
    1: [(540, 570), (600, 1020)],
    2: [(540, 570), (600, 660), (690, 810), (870, 900), (960, 990)]
}

# Helper function: meeting [start, start+duration) must not overlap a busy interval [b_start, b_end).
# Non-overlap is satisfied if the meeting ends on or before the busy interval starts
# or if the meeting starts on or after the busy interval ends.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Try candidate days in the order of Pamela's preference
for day in candidate_days:
    solver = Solver()
    # Ensure meeting is completely within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Amy (if any) on the given day.
    for (b_start, b_end) in amy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add busy constraints for Pamela on the given day.
    for (b_start, b_end) in pamela_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Pamela's preference constraint:
    # On Wednesday, she prefers not to have meetings before 16:00 (i.e., before 960 minutes).
    if day == 2:
        solver.add(start >= 16 * 60)  # 16:00 => 960 minutes
    
    # Search for the earliest valid start time within the allowed work hours.
    # We iterate minute by minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Remove the assumption before breaking.
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM strings.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
        day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")