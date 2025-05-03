from z3 import Solver, Int, Or, sat

# Meeting duration is 30 minutes.
duration = 30

# Work hours in minutes from midnight: 9:00 is 540, 17:00 is 1020.
WORK_START = 9 * 60
WORK_END = 17 * 60

# We'll represent the meeting start time as an integer (in minutes from midnight).
start = Int("start")

# Days are coded as: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# The meeting must be scheduled on one of these days.
# The provided hard constraints:
#   • Natalie cannot meet on Thursday.
#   • Stephen would like to avoid more meetings on Monday and Wednesday.
#   • Stephen would like to avoid meetings on Tuesday that start too late (i.e. after 12:00 so that the meeting would run past 12:30).
#
# Under these constraints, and since a solution must exist, we use Tuesday as the only candidate day.
candidate_days = [1]  # Only Tuesday (day 1)

# Busy schedules (times in minutes from midnight) for Natalie:
# Monday: 11:00-11:30, 16:00-16:30
# Tuesday: 10:00-10:30, 15:00-15:30
# Wednesday: 10:00-10:30, 11:00-11:30, 13:30-14:00, 15:00-15:30
# Thursday: 11:30-12:00, 15:30-16:00
natalie_busy = {
    0: [(660, 690), (960, 990)],
    1: [(600, 630), (900, 930)],
    2: [(600, 630), (660, 690), (810, 840), (900, 930)],
    3: [(690, 720), (930, 960)]
}

# Busy schedules for Stephen:
# Monday: 9:00-9:30, 11:00-13:30, 14:00-15:00, 15:30-16:00
# Tuesday: 9:00-10:00, 10:30-11:30, 12:30-14:00
# Wednesday: 9:00-9:30, 10:00-12:30, 13:00-13:30, 14:30-15:00, 15:30-16:30
# Thursday: 9:30-10:00, 13:30-15:00, 16:00-17:00
stephen_busy = {
    0: [(540, 570), (660, 810), (840, 900), (930, 960)],
    1: [(540, 600), (630, 690), (750, 840)],
    2: [(540, 570), (600, 750), (780, 810), (870, 900), (930, 990)],
    3: [(570, 600), (810, 900), (960, 1020)]
}

# A helper function that returns a Z3 condition ensuring that the meeting time [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# We now iterate over the candidate days.
# In our case, the only candidate is Tuesday (day 1).
for day in candidate_days:
    solver = Solver()
    
    # Meeting must be scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add day-based preferences/constraints:
    # Natalie cannot meet on Thursday => not needed here since day=1 (Tuesday) is our candidate.
    # Stephen prefers to avoid Monday and Wednesday => candidate is Tuesday, so that’s fine.
    # Stephen would like to avoid meetings on Tuesday after 12:30.
    # To ensure the meeting ends by 12:30 (which is 750 minutes), we add:
    if day == 1:  # Tuesday
        solver.add(start + duration <= 750)
    
    # Add busy intervals constraints for Natalie for the given day.
    for interval in natalie_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy intervals constraints for Stephen for the given day.
    for interval in stephen_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Now search for a valid meeting start time minute by minute.
    for t in range(WORK_START, WORK_END - duration + 1):  # possible start times in minutes.
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Remove the temporary constraint before breaking.
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