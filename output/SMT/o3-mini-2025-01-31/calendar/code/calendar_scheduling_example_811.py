from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work day hours in minutes (from midnight): 9:00 is 540 and 17:00 is 1020.
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedules for Theresa (intervals in minutes from midnight)
# Monday: 9:30-10:30, 13:00-13:30
# Tuesday: 10:00-10:30
# Wednesday: 12:00-12:30, 14:30-15:00
# Thursday: 11:00-12:00, 12:30-13:30
theresa_busy = {
    0: [(570, 630), (780, 810)],      # Monday: 9:30-10:30, 13:00-13:30
    1: [(600, 630)],                  # Tuesday: 10:00-10:30
    2: [(720, 750), (870, 900)],        # Wednesday: 12:00-12:30, 14:30-15:00
    3: [(660, 720), (750, 810)]         # Thursday: 11:00-12:00, 12:30-13:30
}

# Busy schedules for Emily (intervals in minutes from midnight)
# Monday: 9:00-10:00, 11:00-12:30, 13:30-14:00, 15:00-15:30
# Tuesday: 10:00-11:00, 14:00-14:30, 15:00-15:30, 16:00-16:30
# Wednesday: 9:00-10:00, 11:00-15:00, 15:30-17:00
# Thursday: 9:00-11:00, 14:30-16:00
emily_busy = {
    0: [(540, 600), (660, 750), (810, 840), (900, 930)],         # Monday
    1: [(600, 660), (840, 870), (900, 930), (960, 990)],           # Tuesday
    2: [(540, 600), (660, 900), (930, 1020)],                      # Wednesday
    3: [(540, 660), (870, 960)]                                    # Thursday
}

# Preference Constraints:
# Theresa cannot meet on Thursday, so day == 3 is not allowed for her.
# Emily cannot meet on Monday or Tuesday, so days 0 and 1 are not allowed for her.
# The group wants to meet at their earliest availability (day and time).
solution_found = False
selected_day = None
selected_start = None

# Helper function to ensure a meeting starting at 'start_var' for 'duration' minutes
# does not overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate through candidate days in order
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)

    # Apply preference constraints on days:
    # Theresa cannot meet on Thursday (day == 3)
    if day == 3:
        solver.add(False)
    # Emily cannot meet on Monday (day == 0) or Tuesday (day == 1)
    if day == 0 or day == 1:
        solver.add(False)
    
    # Add busy intervals constraints for Theresa on the current day
    for (busy_start, busy_end) in theresa_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add busy intervals constraints for Emily on the current day
    for (busy_start, busy_end) in emily_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for an available meeting time by checking minute-by-minute.
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
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")