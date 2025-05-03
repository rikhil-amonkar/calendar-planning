from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Define the meeting start time variable (in minutes from midnight).
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Define days as: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
#
# Preferences based on the task:
# • Judith would like to avoid more meetings on Monday.
# • Judith would like to avoid meetings on Wednesday before 12:00.
#
# We'll try candidate days in this order: Tuesday, Wednesday, then Monday.
candidate_days = [1, 2, 0]

# Judith's busy schedule:
# Monday: 12:00 to 12:30 -> (720, 750)
# Wednesday: 11:30 to 12:00 -> (690, 720)
judith_busy = {
    0: [(720, 750)],
    2: [(690, 720)]
}

# Timothy's busy schedule:
# Monday:
#   9:30 to 10:00 -> (570, 600)
#   10:30 to 11:30 -> (630, 690)
#   12:30 to 14:00 -> (750, 840)
#   15:30 to 17:00 -> (930, 1020)
# Tuesday:
#   9:30 to 13:00 -> (570, 780)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 17:00 -> (870, 1020)
# Wednesday:
#   9:00 to 9:30   -> (540, 570)
#   10:30 to 11:00 -> (630, 660)
#   13:30 to 14:30 -> (810, 870)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 16:30 -> (960, 990)
timothy_busy = {
    0: [(570, 600), (630, 690), (750, 840), (930, 1020)],
    1: [(570, 780), (810, 840), (870, 1020)],
    2: [(540, 570), (630, 660), (810, 870), (900, 930), (960, 990)]
}

# Helper function to ensure no overlap between meeting [start, start+duration)
# and a busy interval [b_start, b_end). The meeting is allowed if it ends at or before
# a busy interval starts, or starts at or after a busy interval ends.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try each candidate day in the order of preference.
for day in candidate_days:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Judith.
    for b_start, b_end in judith_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add busy constraints for Timothy.
    for b_start, b_end in timothy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add additional preference constraint for Wednesday: 
    # Judith wants to avoid meetings before 12:00, so on Wednesday meeting must start at or after 12:00.
    if day == 2:
        solver.add(start >= 12 * 60)  # 12:00 is 720 minutes

    # Check each possible meeting starting minute within work hours.
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
    # Convert minutes to HH:MM format.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")