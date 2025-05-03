from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Create a Z3 integer variable for the meeting start time (in minutes from midnight)
start = Int("start")

# Candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Nicole's busy times (in minutes from midnight):
# Monday: 9:00-9:30 -> (540,570), 13:00-13:30 -> (780,810), 14:30-15:30 -> (870,930)
# Tuesday: 9:00-9:30 -> (540,570), 11:30-13:30 -> (690,810), 14:30-15:30 -> (870,930)
# Wednesday: 10:00-11:00 -> (600,660), 12:30-15:00 -> (750,900), 16:00-17:00 -> (960,1020)
nicole_busy = {
    0: [(540, 570), (780, 810), (870, 930)],
    1: [(540, 570), (690, 810), (870, 930)],
    2: [(600, 660), (750, 900), (960, 1020)]
}

# Ruth's busy times:
# Monday: 9:00-17:00 -> (540,1020)
# Tuesday: 9:00-17:00 -> (540,1020)
# Wednesday: 9:00-10:30 -> (540,630), 11:00-11:30 -> (660,690), 
#            12:00-12:30 -> (720,750), 13:30-15:30 -> (810,930), 16:00-16:30 -> (960,990)
ruth_busy = {
    0: [(540, 1020)],
    1: [(540, 1020)],
    2: [(540, 630), (660, 690), (720, 750), (810, 930), (960, 990)]
}

# Ruth's preference: On Wednesday (day==2), she does not want meetings after 13:30.
# Since the meeting lasts 30 minutes, if scheduled on Wednesday it must finish by 13:30 (810 minutes).
# That implies that for Wednesday: start + duration <= 810.
def ruth_wednesday_preference(day):
    if day == 2:
        return start + duration <= 810
    return True

# A helper function: the meeting interval [start, start+duration)
# must not overlap a busy interval (b_start, b_end).
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Check each candidate day
for day in candidate_days:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If day is Wednesday, enforce Ruth's timing preference.
    solver.add(ruth_wednesday_preference(day))
    
    # Add Nicole's busy constraints for the chosen day.
    for (b_start, b_end) in nicole_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Ruth's busy constraints for the chosen day.
    for (b_start, b_end) in ruth_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try each potential start time (minute-by-minute) within the workday.
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
    # Convert minutes to HH:MM format.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")