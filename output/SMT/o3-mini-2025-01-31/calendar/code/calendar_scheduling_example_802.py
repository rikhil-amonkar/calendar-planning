from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work hours in minutes from midnight: 9:00 is 540 and 17:00 is 1020.
WORK_START = 9 * 60
WORK_END = 17 * 60

# The meeting start time (in minutes from midnight).
start = Int("start")

# Define days as: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Abigail would rather not meet on Tuesday (day==1) and Charlotte does not want to meet on Monday (day==0).
# Hence, we only consider the allowed days: Wednesday (2) and Thursday (3).
candidate_days = [2, 3]

# Busy schedules in minutes.
# Abigail's busy slots:
# Monday (0): 9:00-9:30 -> (540,570), 11:00-11:30 -> (660,690), 15:30-16:00 -> (930,960)
# Wednesday (2): 9:30-10:00 -> (570,600), 10:30-11:00 -> (630,660)
# Thursday (3): 9:00-9:30 -> (540,570), 12:30-13:30 -> (750,810)
abigail_busy = {
    0: [(540,570), (660,690), (930,960)],
    2: [(570,600), (630,660)],
    3: [(540,570), (750,810)]
}

# Charlotte's busy slots:
# Monday (0): 9:30-10:00 -> (570,600), 10:30-11:00 -> (630,660), 13:00-13:30 -> (780,810), 15:00-17:00 -> (900,1020)
# Tuesday (1): 10:30-12:00 -> (630,720), 12:30-13:30 -> (750,810), 14:30-15:00 -> (870,900), 16:30-17:00 -> (990,1020)
# Wednesday (2): 9:00-9:30 -> (540,570), 10:00-11:30 -> (600,690), 12:00-13:30 -> (720,810), 14:00-15:30 -> (840,930), 16:30-17:00 -> (990,1020)
# Thursday (3): 9:00-12:00 -> (540,720), 14:00-14:30 -> (840,870), 16:00-17:00 -> (960,1020)
charlotte_busy = {
    0: [(570,600), (630,660), (780,810), (900,1020)],
    1: [(630,720), (750,810), (870,900), (990,1020)],
    2: [(540,570), (600,690), (720,810), (840,930), (990,1020)],
    3: [(540,720), (840,870), (960,1020)]
}

# Helper function: returns a condition that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterating over allowed days in order: Wednesday then Thursday.
for day in candidate_days:
    solver = Solver()
    # Ensure meeting time is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Abigail's busy constraints for the current day.
    for interval in abigail_busy.get(day, []):
        b_start, b_end = interval
        solver.add(non_overlap(b_start, b_end))
    
    # Add Charlotte's busy constraints for the current day.
    for interval in charlotte_busy.get(day, []):
        b_start, b_end = interval
        solver.add(non_overlap(b_start, b_end))
        
    # Search for the earliest start time (in minutes) for this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Clean up the solver state.
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Converting minutes into HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")