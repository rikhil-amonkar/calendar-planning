from z3 import Solver, Int, Or, sat

# Meeting duration in minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3
# Zachary cannot meet on Tuesday, so we remove Tuesday.
# Also, Edward would like to avoid more meetings on Wednesday and Thursday.
# Therefore, we search in the preferred order: Monday first, then (if necessary) Wednesday then Thursday.
candidate_days = [0, 2, 3]

# Busy schedules for Edward, with times expressed in minutes from midnight.
edward_busy = {
    0: [ (9*60, 9*60+30),      # Monday: 09:00-09:30
         (11*60, 11*60+30),    # Monday: 11:00-11:30
         (14*60+30, 15*60) ],  # Monday: 14:30-15:00
    1: [ (12*60, 13*60),      # Tuesday: 12:00-13:00
         (16*60+30, 17*60) ],  # Tuesday: 16:30-17:00
    2: [ (9*60, 9*60+30),     # Wednesday: 09:00-09:30
         (14*60, 14*60+30) ],  # Wednesday: 14:00-14:30
    3: [ (15*60+30, 16*60),   # Thursday: 15:30-16:00
         (16*60+30, 17*60) ]   # Thursday: 16:30-17:00
}

# Busy schedules for Zachary, in minutes from midnight.
zachary_busy = {
    0: [ (9*60, 10*60),       # Monday: 09:00-10:00
         (10*60+30, 11*60),   # Monday: 10:30-11:00
         (11*60+30, 12*60+30),# Monday: 11:30-12:30
         (14*60, 17*60) ],    # Monday: 14:00-17:00
    1: [ (9*60, 12*60+30),    # Tuesday: 09:00-12:30
         (13*60, 13*60+30),   # Tuesday: 13:00-13:30
         (14*60, 17*60) ],    # Tuesday: 14:00-17:00
    2: [ (9*60, 15*60),       # Wednesday: 09:00-15:00
         (16*60, 17*60) ],    # Wednesday: 16:00-17:00
    3: [ (9*60, 12*60),       # Thursday: 09:00-12:00
         (12*60+30, 14*60),   # Thursday: 12:30-14:00
         (15*60, 17*60) ]     # Thursday: 15:00-17:00
}

# A helper function that creates a constraint ensuring that a meeting
# starting at time s (with fixed duration) does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# We iterate through candidate days in the preference order.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes from midnight
    
    # Ensure meeting is within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add Edward's busy constraints for the day.
    for busy_start, busy_end in edward_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
        
    # Add Zachary's busy constraints for the day.
    for busy_start, busy_end in zachary_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Search minute-by-minute for the earliest time.
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
    # Convert minutes into HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")