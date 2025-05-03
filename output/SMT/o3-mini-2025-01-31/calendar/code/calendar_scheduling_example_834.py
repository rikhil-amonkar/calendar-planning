from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Encode days as: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]  # Check days in order (earliest availability)

# Busy intervals for each participant (intervals defined as [start, end) in minutes)
# Joseph's busy schedule:
# Monday: 9:00-9:30 -> (540,570)
#         10:30-12:00 -> (630,720)
#         12:30-13:30 -> (750,810)
#         15:00-15:30 -> (900,930)
#         16:30-17:00 -> (990,1020)
# Tuesday: 10:30-11:00 -> (630,660)
#          11:30-13:00 -> (690,780)
#          15:30-17:00 -> (930,1020)
# Wednesday: 9:00-10:00 -> (540,600)
#            11:00-12:00 -> (660,720)
#            12:30-13:00 -> (750,780)
#            13:30-14:00 -> (810,840)
#            14:30-15:00 -> (870,900)
#            15:30-16:00 -> (930,960)
# Thursday: 10:30-11:00 -> (630,660)
#           11:30-12:30 -> (690,750)
#           13:00-13:30 -> (780,810)
#           15:00-15:30 -> (900,930)
joseph_busy = {
    0: [(540,570), (630,720), (750,810), (900,930), (990,1020)],
    1: [(630,660), (690,780), (930,1020)],
    2: [(540,600), (660,720), (750,780), (810,840), (870,900), (930,960)],
    3: [(630,660), (690,750), (780,810), (900,930)]
}

# Donna's busy schedule:
# Monday: 9:00-10:30 -> (540,630)
#         12:00-12:30 -> (720,750)
#         14:00-15:00 -> (840,900)
#         16:30-17:00 -> (990,1020)
# Tuesday: 10:30-11:00 -> (630,660)
#          11:30-12:00 -> (690,720)
#          12:30-14:00 -> (750,840)
#          15:00-17:00 -> (900,1020)
# Wednesday: 9:00-10:30 -> (540,630)
#            12:00-14:30 -> (720,870)
#            15:30-16:00 -> (930,960)
#            16:30-17:00 -> (990,1020)
# Thursday: 9:30-11:00 -> (570,660)
#           13:00-14:00 -> (780,840)
#           14:30-15:00 -> (870,900)
#           16:00-17:00 -> (960,1020)
donna_busy = {
    0: [(540,630), (720,750), (840,900), (990,1020)],
    1: [(630,660), (690,720), (750,840), (900,1020)],
    2: [(540,630), (720,870), (930,960), (990,1020)],
    3: [(570,660), (780,840), (870,900), (960,1020)]
}

# Function to generate the constraint that a meeting starting at time s (lasting 'duration') 
# does not overlap with a busy interval [b_start, b_end)
def no_overlap(b_start, b_end, s):
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days (Monday, Tuesday, Wednesday, Thursday)
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes
    
    # The meeting must fully fit within working hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add constraints for Joseph's busy intervals on this day.
    for interval in joseph_busy.get(day, []):
        b_start, b_end = interval
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add constraints for Donna's busy intervals on this day.
    for interval in donna_busy.get(day, []):
        b_start, b_end = interval
        solver.add(no_overlap(b_start, b_end, s))
    
    # Find the earliest available start time by checking each minute within the work window.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Remove the pushed context.
            break
        solver.pop()
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")