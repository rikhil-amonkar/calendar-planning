from z3 import Solver, Int, Or, sat

# Meeting duration in minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# All days in the window:
all_days = [0, 1, 2, 3]

# Preferences:
# • Michelle would like to avoid more meetings on Wednesday -> skip day 2.
# • Sara would rather not meet on Monday and Tuesday -> skip days 0 and 1.
# For this solution, we enforce these as hard constraints.
candidate_days = [d for d in all_days if d not in [2, 0, 1]]
# That leaves candidate_days = [3] (i.e., Thursday)

# Busy schedules of Michelle (each time in minutes from midnight)
michelle_busy = {
    0: [ (11 * 60, 11 * 60 + 30),   # Monday: 11:00 to 11:30
         (16 * 60, 16 * 60 + 30) ],  # Monday: 16:00 to 16:30
    1: [ (10 * 60, 11 * 60),         # Tuesday: 10:00 to 11:00
         (11 * 60 + 30, 12 * 60 + 30),# Tuesday: 11:30 to 12:30
         (14 * 60, 15 * 60),         # Tuesday: 14:00 to 15:00
         (15 * 60 + 30, 16 * 60) ],   # Tuesday: 15:30 to 16:00
    2: [ (10 * 60 + 30, 11 * 60),     # Wednesday: 10:30 to 11:00
         (11 * 60 + 30, 13 * 60),     # Wednesday: 11:30 to 13:00
         (13 * 60 + 30, 15 * 60),     # Wednesday: 13:30 to 15:00
         (16 * 60 + 30, 17 * 60) ],   # Wednesday: 16:30 to 17:00
    3: [ (9 * 60 + 30, 10 * 60 + 30),  # Thursday: 09:30 to 10:30
         (12 * 60, 12 * 60 + 30),      # Thursday: 12:00 to 12:30
         (13 * 60, 13 * 60 + 30),      # Thursday: 13:00 to 13:30
         (15 * 60 + 30, 17 * 60) ]     # Thursday: 15:30 to 17:00
}

# Busy schedules of Sara (each time in minutes from midnight)
sara_busy = {
    0: [ (9 * 60, 11 * 60 + 30),      # Monday: 09:00 to 11:30
         (12 * 60, 12 * 60 + 30),     # Monday: 12:00 to 12:30
         (13 * 60, 13 * 60 + 30),     # Monday: 13:00 to 13:30
         (14 * 60, 17 * 60) ],        # Monday: 14:00 to 17:00
    1: [ (10 * 60 + 30, 11 * 60 + 30), # Tuesday: 10:30 to 11:30
         (12 * 60, 12 * 60 + 30),     # Tuesday: 12:00 to 12:30
         (13 * 60, 13 * 60 + 30),     # Tuesday: 13:00 to 13:30
         (14 * 60, 15 * 60) ],        # Tuesday: 14:00 to 15:00
    2: [ (9 * 60, 12 * 60 + 30),      # Wednesday: 09:00 to 12:30
         (13 * 60, 14 * 60 + 30),     # Wednesday: 13:00 to 14:30
         (15 * 60, 16 * 60) ],        # Wednesday: 15:00 to 16:00
    3: [ (9 * 60, 11 * 60),          # Thursday: 09:00 to 11:00
         (11 * 60 + 30, 12 * 60 + 30),# Thursday: 11:30 to 12:30
         (13 * 60 + 30, 14 * 60),     # Thursday: 13:30 to 14:00
         (15 * 60, 17 * 60) ]         # Thursday: 15:00 to 17:00
}

# Utility function: given a meeting starting at time s (for a duration) and a busy interval [busy_start, busy_end),
# the meeting does not overlap with the busy interval if:
#   s + duration <= busy_start  or  s >= busy_end
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Since we want the earliest availability, we sort candidate days in natural order.
for day in sorted(candidate_days):
    solver = Solver()
    s = Int("s")  # meeting start time in minutes from midnight

    # Meeting must be within working hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)

    # Add busy constraints for Michelle for the chosen day.
    for busy_start, busy_end in michelle_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add busy constraints for Sara for the chosen day.
    for busy_start, busy_end in sara_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # We'll search for the earliest start time (minute by minute).
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