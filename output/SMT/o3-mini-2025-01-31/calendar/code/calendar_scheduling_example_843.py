from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Encode days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Cynthia's busy schedule (times in minutes from midnight):
# Monday: 10:00-10:30 -> (600, 630)
# Tuesday: no busy meetings mentioned
# Wednesday: 9:30-10:00 -> (570, 600)
# Thursday: 10:30-11:00 -> (630, 660) and 12:00-12:30 -> (720, 750)
cynthia_busy = {
    0: [(600, 630)],
    1: [],
    2: [(570, 600)],
    3: [(630, 660), (720, 750)]
}

# Willie's busy schedule (times in minutes from midnight):
# Monday: 9:30-11:00 -> (570, 660), 12:00-14:00 -> (720, 840), 16:30-17:00 -> (990, 1020)
# Tuesday: 9:00-9:30 -> (540, 570), 10:30-11:00 -> (630, 660), 12:30-16:30 -> (750, 990)
# Wednesday: 9:00-10:00 -> (540, 600), 10:30-11:30 -> (630, 690), 12:00-14:30 -> (720, 870),
#            15:30-16:00 -> (930, 960), 16:30-17:00 -> (990, 1020)
# Thursday: 9:00-10:30 -> (540, 630), 11:30-12:30 -> (690, 750), 13:30-15:30 -> (810, 930)
willie_busy = {
    0: [(570, 660), (720, 840), (990, 1020)],
    1: [(540, 570), (630, 660), (750, 990)],
    2: [(540, 600), (630, 690), (720, 870), (930, 960), (990, 1020)],
    3: [(540, 630), (690, 750), (810, 930)]
}

# Utility function to ensure the meeting [s, s+duration] does NOT overlap any busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days (in order Monday, Tuesday, Wednesday, Thursday)
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes

    # Meeting must be within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)

    # Add Cynthia's busy constraints for that day.
    for (b_start, b_end) in cynthia_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add Willie's busy constraints for that day.
    for (b_start, b_end) in willie_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # We search for the earliest minute that allows a meeting.
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
    # Convert minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")