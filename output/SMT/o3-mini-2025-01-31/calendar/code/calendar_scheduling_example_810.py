from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work day hours in minutes (from midnight): 9:00 is 540 and 17:00 is 1020.
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedules are expressed as intervals (start, end) in minutes from midnight.
# Nicole's schedule:
nicole_busy = {
    0: [(570, 660),  # Monday: 9:30-11:00
        (720, 780),  # Monday: 12:00-13:00
        (810, 990)], # Monday: 13:30-16:30
    1: [(540, 570),  # Tuesday: 9:00-9:30
        (630, 660),  # Tuesday: 10:30-11:00
        (690, 750),  # Tuesday: 11:30-12:30
        (840, 1020)],# Tuesday: 14:00-17:00
    2: [(540, 570),  # Wednesday: 9:00-9:30
        (600, 660),  # Wednesday: 10:00-11:00
        (690, 720),  # Wednesday: 11:30-12:00
        (750, 900),  # Wednesday: 12:30-15:00
        (930, 990)], # Wednesday: 15:30-16:30
    3: [(540, 570),  # Thursday: 9:00-9:30
        (630, 660),  # Thursday: 10:30-11:00
        (720, 750),  # Thursday: 12:00-12:30
        (810, 870),  # Thursday: 13:30-14:30
        (900, 930),  # Thursday: 15:00-15:30
        (960, 1020)] # Thursday: 16:00-17:00
}

# Joe's schedule:
# Joe is free the entire week, so no busy intervals.

# Preference Constraints:
# Joe would like to avoid more meetings on Thursday.
# Nicole would rather not meet on Tuesday.
#
# We enforce these preferences as hard constraints in our scheduling:
#   - For Joe, do not schedule on Thursday (day == 3).
#   - For Nicole, do not schedule on Tuesday (day == 1).

solution_found = False
selected_day = None
selected_start = None

# Helper function to enforce that a meeting starting at "start_var" (lasting duration minutes)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate over candidate days.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply the preference constraints for Joe and Nicole.
    if day == 3:  # Thursday: Joe wants to avoid meetings
        solver.add(False)
    if day == 1:  # Tuesday: Nicole would rather not meet
        solver.add(False)
    
    # Since Joe is free, we don't add busy constraints for him.
    # Add Nicole's busy intervals constraints for the day.
    for (busy_start, busy_end) in nicole_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Now, look for a valid start time by iterating minute-by-minute:
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