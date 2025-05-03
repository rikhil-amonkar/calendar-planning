from z3 import Solver, Int, Or, sat

# Meeting duration is 60 minutes.
duration = 60

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes).
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Bradley's busy schedule in minutes from midnight.
# Monday:
#  9:00-9:30   -> (540,570)
#  10:30-11:00 -> (630,660)
#  12:00-13:00 -> (720,780)
#  14:00-14:30 -> (840,870)
# Tuesday:
#  9:30-10:00  -> (570,600)
#  11:00-11:30 -> (660,690)
#  13:30-14:00 -> (810,840)
#  16:00-16:30 -> (960,990)
# Wednesday:
#  11:00-11:30 -> (660,690)
#  12:00-12:30 -> (720,750)
#  13:00-14:00 -> (780,840)
#  16:00-16:30 -> (960,990)
# Thursday:
#  9:00-9:30   -> (540,570)
#  10:00-11:00 -> (600,660)
#  11:30-12:00 -> (690,720)
#  12:30-13:00 -> (750,780)
#  14:30-17:00 -> (870,1020)
bradley_busy = {
    0: [(540,570), (630,660), (720,780), (840,870)],
    1: [(570,600), (660,690), (810,840), (960,990)],
    2: [(660,690), (720,750), (780,840), (960,990)],
    3: [(540,570), (600,660), (690,720), (750,780), (870,1020)]
}

# Bruce's busy schedule in minutes from midnight.
# Monday:
#  9:00-9:30   -> (540,570)
#  10:00-17:00 -> (600,1020)
# Tuesday:
#  9:30-14:00  -> (570,840)
#  15:00-17:00 -> (900,1020)
# Wednesday:
#  10:00-10:30 -> (600,630)
#  12:30-13:30 -> (750,810)
#  14:30-16:00 -> (870,960)
#  16:30-17:00 -> (990,1020)
# Thursday:
#  12:30-14:30 -> (750,870)
#  15:00-15:30 -> (900,930)
#  16:00-17:00 -> (960,1020)
bruce_busy = {
    0: [(540,570), (600,1020)],
    1: [(570,840), (900,1020)],
    2: [(600,630), (750,810), (870,960), (990,1020)],
    3: [(750,870), (900,930), (960,1020)]
}

# Function to ensure the meeting starting at s (with duration) does not overlap a busy interval.
def no_overlap(busy_start, busy_end, s):
    # Meeting [s, s+duration) doesn't overlap [busy_start, busy_end)
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# We iterate over the candidate days in order for earliest meeting possibility.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes
    # Constrain meeting to be within working hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add Bradley's busy constraints for the day.
    for busy_interval in bradley_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add Bruce's busy constraints for the day.
    for busy_interval in bruce_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Search for the earliest valid start time in the day (minute-by-minute).
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
    # Convert minutes to HH:MM string format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")