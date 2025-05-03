from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Christopher's busy schedule (in minutes from midnight):
# Monday:    10:00-10:30 -> (600,630), 11:00-11:30 -> (660,690),
#            12:30-13:00 -> (750,780), 16:00-16:30 -> (960,990)
# Tuesday:   9:00-10:00  -> (540,600), 10:30-11:00 -> (630,660),
#            11:30-12:00 -> (690,720), 12:30-13:00 -> (750,780),
#            13:30-15:30 -> (810,930), 16:30-17:00 -> (990,1020)
# Wednesday: 10:00-10:30 -> (600,630), 11:00-11:30 -> (660,690),
#            13:00-14:00 -> (780,840), 14:30-15:00 -> (870,900),
#            15:30-16:00 -> (930,960), 16:30-17:00 -> (990,1020)
# Thursday:  10:30-11:30 -> (630,690), 16:00-16:30 -> (960,990)
christopher_busy = {
    0: [(600,630), (660,690), (750,780), (960,990)],
    1: [(540,600), (630,660), (690,720), (750,780), (810,930), (990,1020)],
    2: [(600,630), (660,690), (780,840), (870,900), (930,960), (990,1020)],
    3: [(630,690), (960,990)]
}

# Deborah's busy schedule (in minutes from midnight):
# Monday:    9:00-17:00 -> (540,1020)
# Tuesday:   9:00-10:30  -> (540,630), 11:30-13:00 -> (690,780),
#            14:30-15:30 -> (870,930), 16:00-17:00 -> (960,1020)
# Wednesday: 9:00-11:30  -> (540,690), 13:00-13:30 -> (780,810),
#            14:00-15:00 -> (840,900), 15:30-16:00 -> (930,960),
#            16:30-17:00 -> (990,1020)
# Thursday:  9:30-10:00  -> (570,600), 10:30-13:00 -> (630,780),
#            13:30-16:30 -> (810,990)
deborah_busy = {
    0: [(540,1020)],
    1: [(540,630), (690,780), (870,930), (960,1020)],
    2: [(540,690), (780,810), (840,900), (930,960), (990,1020)],
    3: [(570,600), (630,780), (810,990)]
}

# Utility function to ensure the meeting [s, s+duration] does NOT overlap any busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order: Monday, Tuesday, Wednesday, Thursday.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time (in minutes)
    
    # Add constraint: Meeting must occur within the work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add Christopher's busy constraints for the day:
    for (busy_start, busy_end) in christopher_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add Deborah's busy constraints for the day:
    for (busy_start, busy_end) in deborah_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Now iterate over each potential start time within work hours to find the earliest valid time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
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
    # Convert minutes to HH:MM.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")