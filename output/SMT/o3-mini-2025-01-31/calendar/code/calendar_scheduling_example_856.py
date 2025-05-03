from z3 import Solver, Int, Or, sat

# Meeting duration in minutes
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3
all_days = [0, 1, 2, 3]

# Busy schedules for Dennis (times in minutes from midnight)
dennis_busy = {
    0: [ (9 * 60, 9 * 60 + 30),     # Monday: 9:00 to 9:30
         (10 * 60 + 30, 11 * 60),   # Monday: 10:30 to 11:00
         (11 * 60 + 30, 12 * 60 + 30), # Monday: 11:30 to 12:30
         (13 * 60 + 30, 14 * 60 + 30), # Monday: 13:30 to 14:30
         (15 * 60, 15 * 60 + 30)],     # Monday: 15:00 to 15:30
    1: [ (10 * 60, 10 * 60 + 30),   # Tuesday: 10:00 to 10:30
         (11 * 60, 12 * 60),         # Tuesday: 11:00 to 12:00
         (13 * 60, 13 * 60 + 30),    # Tuesday: 13:00 to 13:30
         (14 * 60, 14 * 60 + 30),    # Tuesday: 14:00 to 14:30
         (16 * 60, 16 * 60 + 30)],   # Tuesday: 16:00 to 16:30
    2: [ (9 * 60 + 30, 10 * 60),    # Wednesday: 9:30 to 10:00
         (10 * 60 + 30, 11 * 60),    # Wednesday: 10:30 to 11:00
         (13 * 60, 13 * 60 + 30),    # Wednesday: 13:00 to 13:30
         (14 * 60, 15 * 60),         # Wednesday: 14:00 to 15:00
         (16 * 60 + 30, 17 * 60)],   # Wednesday: 16:30 to 17:00
    3: [ (9 * 60 + 30, 10 * 60),    # Thursday: 9:30 to 10:00
         (10 * 60 + 30, 12 * 60),    # Thursday: 10:30 to 12:00
         (13 * 60, 14 * 60 + 30),    # Thursday: 13:00 to 14:30
         (15 * 60 + 30, 16 * 60 + 30)]# Thursday: 15:30 to 16:30
}

# Busy schedules for William (times in minutes from midnight)
william_busy = {
    0: [ (9 * 60, 17 * 60) ],         # Monday: 9:00 to 17:00 (fully busy)
    1: [ (9 * 60, 12 * 60),            # Tuesday: 9:00 to 12:00
         (12 * 60 + 30, 15 * 60 + 30),  # Tuesday: 12:30 to 15:30
         (16 * 60, 17 * 60) ],         # Tuesday: 16:00 to 17:00
    2: [ (9 * 60, 11 * 60 + 30),       # Wednesday: 9:00 to 11:30
         (12 * 60, 12 * 60 + 30),      # Wednesday: 12:00 to 12:30
         (13 * 60, 15 * 60),           # Wednesday: 13:00 to 15:00
         (16 * 60, 17 * 60) ],         # Wednesday: 16:00 to 17:00
    3: [ (9 * 60, 17 * 60) ]           # Thursday: 9:00 to 17:00 (fully busy)
}

# Utility function: The meeting starting at time s (with fixed duration) does not overlap with a busy interval
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over the days in order (Monday, Tuesday, Wednesday, Thursday)
for day in sorted(all_days):
    solver = Solver()
    s = Int("s")  # meeting start time in minutes from midnight

    # Meeting must be within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)

    # Add Dennis' busy constraints for the day.
    for busy_start, busy_end in dennis_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))

    # Add William's busy constraints for the day.
    for busy_start, busy_end in william_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))

    # Try to find an earliest available time slot minute by minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
        if solver.check() == sat:
            selected_day = day
            selected_start = t
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