from z3 import Solver, Int, Or, sat

# Meeting duration in minutes.
duration = 30

# Define work hours in minutes from midnight.
WORK_START = 9 * 60   # 540 minutes (9:00)
WORK_END = 17 * 60    # 1020 minutes (17:00)

# Create Z3 integer variable for meeting start time (in minutes from midnight).
start = Int("start")

# Define days:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# The meeting can be scheduled on any of these days.
# Since we want the earliest availability, we will explore days in the natural order: Monday, then Tuesday, then Wednesday.
candidate_days = [0, 1, 2]

# Larry's busy schedule. Each tuple (b_start, b_end) represents a blocked interval in minutes.
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:00 -> (690, 720)
#   14:00 to 14:30 -> (840, 870)
# Tuesday:
#   9:30 to 10:30   -> (570, 630)
#   11:30 to 12:00  -> (690, 720)
#   13:30 to 14:00  -> (810, 840)
#   14:30 to 15:00  -> (870, 900)
#   16:30 to 17:00  -> (990, 1020)
# Wednesday:
#   9:00 to 9:30   -> (540, 570)
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 16:30 -> (810, 990)
larry_busy = {
    0: [(600, 630), (690, 720), (840, 870)],
    1: [(570, 630), (690, 720), (810, 840), (870, 900), (990, 1020)],
    2: [(540, 570), (660, 690), (720, 750), (810, 990)]
}

# Philip's busy schedule.
# Monday:
#   9:30 to 11:30  -> (570, 690)
#   12:00 to 17:00 -> (720, 1020)
# Tuesday:
#   9:30 to 10:30  -> (570, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 13:30 -> (720, 810)
#   14:00 to 15:30 -> (840, 930)
#   16:00 to 16:30 -> (960, 990)
# Wednesday:
#   9:00 to 10:00  -> (540, 600)
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
#   15:00 to 15:30 -> (900, 930)
#   16:30 to 17:00 -> (990, 1020)
philip_busy = {
    0: [(570, 690), (720, 1020)],
    1: [(570, 630), (660, 690), (720, 810), (840, 930), (960, 990)],
    2: [(540, 600), (720, 750), (780, 810), (900, 930), (990, 1020)]
}

# Helper function to express that the meeting should not overlap a given busy interval.
# For a busy interval [b_start, b_end) the meeting [start, start+duration) should either finish
# before the busy interval begins or start after the busy interval ends.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order: Monday, Tuesday, then Wednesday.
for day in candidate_days:
    solver = Solver()
    # Ensure the meeting is completely within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Larry's busy constraints for the given day.
    for (b_start, b_end) in larry_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Philip's busy constraints for the given day.
    for (b_start, b_end) in philip_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Explore all possible start times (from WORK_START to WORK_END - duration)
    # and choose the earliest valid one.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # Pop the push before breaking out.
            break
        solver.pop()
    
    if found:
        break

if found:
    selected_end = selected_start + duration
    # Convert minutes into HH:MM format.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("The earliest available meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
        day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No available meeting time could be found that satisfies all constraints.")