from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Marilyn’s preference: she would rather not meet on Wednesday after 14:00,
# and she has a hint regarding Thursday.
# We encode the Wednesday restriction as: if the meeting is on Wednesday (day==2),
# the meeting must finish by 14:00 (i.e. start + duration <= 14:00 which is 840 minutes).
# We also treat Thursday as a preferred day if possible.
# We'll try candidate days in this order: Thursday, Wednesday, Monday, then Tuesday.
candidate_days = [3, 2, 0, 1]

# Larry's busy intervals (in minutes) by day:
# Monday: 9:00-9:30, 10:00-12:00, 13:00-13:30, 16:30-17:00
# Tuesday: 9:00-9:30, 12:30-17:00
# Wednesday: 9:30-11:00, 11:30-12:00, 13:00-13:30, 16:30-17:00
# Thursday: 9:30-10:00, 13:30-14:00, 16:30-17:00
larry_busy = {
    0: [(540,570), (600,720), (780,810), (990,1020)],
    1: [(540,570), (750,1020)],
    2: [(570,660), (690,720), (780,810), (990,1020)],
    3: [(570,600), (810,840), (990,1020)]
}

# Marilyn's busy intervals (in minutes) by day:
# Monday: 9:00-10:30, 11:30-13:00, 14:00-14:30, 15:00-17:00
# Tuesday: 9:00-11:30, 12:00-13:00, 13:30-14:00, 15:00-16:30
# Wednesday: 9:00-12:00, 13:00-13:30, 14:00-14:30, 16:00-16:30
# Thursday: 9:30-10:30, 12:30-14:30, 15:00-16:30
marilyn_busy = {
    0: [(540,630), (690,780), (840,870), (900,1020)],
    1: [(540,690), (720,780), (810,840), (900,990)],
    2: [(540,720), (780,810), (840,870), (960,990)],
    3: [(570,630), (750,870), (900,990)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function to ensure that a meeting starting at 'start_var' of length "duration"
# does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# We'll check for each candidate day in order, and within that, each minute of the day
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Marilyn's constraint for Wednesday: "would rather not meet on Wednesday after 14:00."
    # We ensure that if day is Wednesday, the meeting finishes by 14:00 (840 minutes).
    if day == 2:
        solver.add(start + duration <= 840)
    
    # Add Larry's busy intervals for the day.
    for (b_start, b_end) in larry_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Add Marilyn's busy intervals for the day.
    for (b_start, b_end) in marilyn_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Try each minute in the work day to find the earliest valid start time on this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Pop the last constraint before breaking out.
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