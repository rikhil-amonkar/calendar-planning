from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Days are encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Anna's busy schedule (times in minutes from midnight):
# Monday:
#    10:30 to 11:00 -> (630, 660)
#    12:30 to 13:00 -> (750, 780)
#    14:00 to 14:30 -> (840, 870)
# Tuesday:
#    10:30 to 11:00 -> (630, 660)
#    13:00 to 13:30 -> (780, 810)
#    14:00 to 14:30 -> (840, 870)
#    16:00 to 16:30 -> (960, 990)
# Wednesday:
#    10:00 to 10:30 -> (600, 630)
#    12:00 to 12:30 -> (720, 750)
#    13:00 to 13:30 -> (780, 810)
#    14:00 to 14:30 -> (840, 870)
#    16:30 to 17:00 -> (990,1020)
# Thursday:
#    10:30 to 11:00 -> (630, 660)
#    12:00 to 13:00 -> (720, 780)
#    16:00 to 16:30 -> (960, 990)
anna_busy = {
    0: [(630, 660), (750, 780), (840, 870)],
    1: [(630, 660), (780, 810), (840, 870), (960, 990)],
    2: [(600, 630), (720, 750), (780, 810), (840, 870), (990, 1020)],
    3: [(630, 660), (720, 780), (960, 990)]
}

# Christian's busy schedule (times in minutes from midnight):
# Monday:
#    9:00 to 13:00  -> (540, 780)
#    13:30 to 16:30 -> (810, 990)
# Tuesday:
#    9:00 to 17:00  -> (540,1020)
# Wednesday:
#    9:00 to 17:00  -> (540,1020)
# Thursday:
#    9:00 to 9:30   -> (540,570)
#    10:00 to 10:30 -> (600,630)
#    11:30 to 14:30 -> (690,870)
#    16:00 to 17:00 -> (960,1020)
christian_busy = {
    0: [(540, 780), (810, 990)],
    1: [(540, 1020)],
    2: [(540, 1020)],
    3: [(540, 570), (600, 630), (690, 870), (960, 1020)]
}

# Utility function: Given a busy interval [busy_start, busy_end) and a meeting starting time s (with duration),
# the meeting does not overlap the busy interval if it finishes by busy_start or starts at/after busy_end.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days (Monday, Tuesday, Wednesday, Thursday).
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes.

    # Ensure the meeting is within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)

    # Add Anna's busy constraints for the day.
    for (busy_start, busy_end) in anna_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))

    # Add Christian's busy constraints for the day.
    for (busy_start, busy_end) in christian_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))

    # Search for the earliest possible start time (minute-wise).
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