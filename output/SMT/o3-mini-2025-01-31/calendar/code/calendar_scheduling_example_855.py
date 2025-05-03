from z3 import Solver, Int, Or, sat

# Meeting duration (in minutes)
duration = 30

# Work hours (in minutes from midnight)
WORK_START = 9 * 60    # 09:00 -> 540 minutes
WORK_END = 17 * 60     # 17:00 -> 1020 minutes

# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3
all_days = [0, 1, 2, 3]

# Russell's preferences:
# "Russell do not want to meet on Tuesday. Wednesday. Thursday after 11:00."
# So we exclude Tuesday (1) and Wednesday (2). For Thursday (3) we only allow meetings
# that start before 11:00.
candidate_days = [d for d in all_days if d not in [1, 2]]

# Busy schedules for Andrea (times in minutes from midnight).
# Each tuple is (start, end)
andrea_busy = {
    0: [ (11 * 60 + 30, 12 * 60),    # Monday: 11:30 to 12:00
         (12 * 60 + 30, 13 * 60),    # Monday: 12:30 to 13:00
         (13 * 60 + 30, 14 * 60),    # Monday: 13:30 to 14:00
         (15 * 60, 16 * 60),         # Monday: 15:00 to 16:00
         (16 * 60 + 30, 17 * 60)],   # Monday: 16:30 to 17:00
    1: [ (11 * 60 + 30, 12 * 60),    # Tuesday: 11:30 to 12:00
         (12 * 60 + 30, 13 * 60)],   # Tuesday: 12:30 to 13:00
    2: [ (11 * 60 + 30, 12 * 60),    # Wednesday: 11:30 to 12:00
         (12 * 60 + 30, 13 * 60),    # Wednesday: 12:30 to 13:00
         (14 * 60 + 30, 17 * 60)],   # Wednesday: 14:30 to 17:00
    3: [ (10 * 60 + 30, 11 * 60),    # Thursday: 10:30 to 11:00
         (12 * 60 + 30, 13 * 60),    # Thursday: 12:30 to 13:00
         (16 * 60, 16 * 60 + 30)]    # Thursday: 16:00 to 16:30
}

# Busy schedules for Russell (times in minutes from midnight).
russell_busy = {
    0: [ (9 * 60, 15 * 60 + 30),     # Monday: 09:00 to 15:30
         (16 * 60, 17 * 60) ],       # Monday: 16:00 to 17:00
    1: [ (9 * 60 + 30, 11 * 60),     # Tuesday: 09:30 to 11:00
         (11 * 60 + 30, 12 * 60),    # Tuesday: 11:30 to 12:00
         (12 * 60 + 30, 13 * 60),    # Tuesday: 12:30 to 13:00
         (14 * 60, 17 * 60) ],       # Tuesday: 14:00 to 17:00
    2: [ (9 * 60, 9 * 60 + 30),      # Wednesday: 09:00 to 09:30
         (10 * 60 + 30, 11 * 60),    # Wednesday: 10:30 to 11:00
         (11 * 60 + 30, 15 * 60),    # Wednesday: 11:30 to 15:00
         (15 * 60 + 30, 16 * 60),    # Wednesday: 15:30 to 16:00
         (16 * 60 + 30, 17 * 60)],   # Wednesday: 16:30 to 17:00
    3: [ (9 * 60, 10 * 60),         # Thursday: 09:00 to 10:00
         (11 * 60 + 30, 17 * 60)]    # Thursday: 11:30 to 17:00
}

# A helper function to enforce that a meeting starting at time s (with duration) does not overlap
# with a busy interval [busy_start, busy_end). The condition is either:
#   meeting ends by busy_start OR meeting starts after busy_end.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# We iterate over candidate days in natural order (Monday first, then Thursday)
for day in sorted(candidate_days):
    solver = Solver()
    s = Int("s")  # meeting start time in minutes from midnight

    # Enforce meeting is within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)

    # For Russell's preference on Thursday: meeting should not be scheduled "after 11:00"
    # We interpret that as the meeting must start before 11:00 on Thursday.
    if day == 3:
        solver.add(s < 11 * 60)  # s must be before 11:00 (i.e., less than 660)

    # Add Andrea's busy constraints for the day.
    for busy_start, busy_end in andrea_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add Russell's busy constraints for the day.
    for busy_start, busy_end in russell_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Try to find the earliest start time slot (minute by minute).
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
    # Convert minute based times to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")