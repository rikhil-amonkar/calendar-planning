from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours: 9:00 to 17:00 in minutes since midnight.
WORK_START = 9 * 60      # 540
WORK_END   = 17 * 60     # 1020

# Days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# However, Natalie does not want to meet on Thursday so we only consider Monday to Wednesday.
candidate_days = [0, 1, 2]

# Jonathan's busy schedule (in minutes from midnight):
# Monday: 13:00-14:00 => (780,840), 16:30-17:00 => (990,1020)
# Tuesday: 10:00-11:00 => (600,660), 12:00-12:30 => (720,750), 15:00-15:30 => (900,930), 16:00-16:30 => (960,990)
# Wednesday: 11:30-12:00 => (690,720), 13:00-13:30 => (780,810), 15:00-15:30 => (900,930)
# Thursday: 12:30-13:30 => (750,810), 14:00-14:30 => (840,870)
jonathan_busy = {
    0: [(780, 840), (990, 1020)],
    1: [(600, 660), (720, 750), (900, 930), (960, 990)],
    2: [(690, 720), (780, 810), (900, 930)],
    3: [(750, 810), (840, 870)]
}

# Natalie's busy schedule:
# Monday: 9:00-10:00 => (540,600), 11:00-12:00 => (660,720), 12:30-13:30 => (750,810),
#         14:00-15:00 => (840,900), 16:00-17:00 => (960,1020)
# Tuesday: 9:00-10:00 => (540,600), 10:30-15:30 => (630,930), 16:00-17:00 => (960,1020)
# Wednesday: 9:00-10:30 => (540,630), 11:00-12:00 => (660,720), 13:00-15:00 => (780,900), 15:30-17:00 => (930,1020)
# Thursday: 10:00-12:00 => (600,720), 13:30-14:30 => (810,870), 15:00-15:30 => (900,930), 16:30-17:00 => (990,1020)
natalie_busy = {
    0: [(540, 600), (660, 720), (750, 810), (840, 900), (960, 1020)],
    1: [(540, 600), (630, 930), (960, 1020)],
    2: [(540, 630), (660, 720), (780, 900), (930, 1020)],
    3: [(600, 720), (810, 870), (900, 930), (990, 1020)]
}

# Additional preferences:
# Jonathan prefers not to meet on Monday after 15:00.
# --> If the meeting is on Monday (day==0), then the meeting must end by 15:00 (i.e. start + duration <= 15:00).
# Natalie does not want to meet on Thursday, so we do not consider Thursday (day==3).

# Helper function: ensure that a meeting scheduled at "start" (for a given duration) does not overlap a busy block.
def non_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order (Monday, Tuesday, Wednesday) to find earliest available time.
for day in candidate_days:
    solver = Solver()
    
    # Define the meeting start time variable (in minutes from midnight).
    start = Int("start")
    
    # Basic working hours constraint.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add extra constraint for Jonathan's preference: on Monday, meeting must finish by 15:00.
    if day == 0:
        solver.add(start + duration <= 15 * 60)  # 15:00 is 900 minutes.
    
    # Add non-overlap constraints for Jonathan's busy intervals on the chosen day.
    for interval in jonathan_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    # Add non-overlap constraints for Natalie's busy intervals on the chosen day.
    for interval in natalie_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end, start))
    
    # To get the earliest time on that day, iterate minute by minute from the workday start.
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
    # Convert meeting times from minutes to HH:MM format.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")