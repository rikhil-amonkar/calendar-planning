from z3 import Solver, Int, Or, sat

# Meeting duration in minutes.
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Define days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# We'll check candidates in an order that favors a solution meeting Thomas's preference.
# Thomas would like to avoid meetings on Tuesday before 11:30.
# Given the busy schedules below, Tuesday is the only day with some available slot.
# However, we'll list all days to keep the structure general.
candidate_days = [1, 0, 2, 3]

# Busy schedules for Thomas.
# Times are in minutes from midnight.
thomas_busy = {
    0: [(11 * 60, 11 * 60 + 30),    # Monday 11:00 to 11:30 -> (660,690)
        (12 * 60 + 30, 13 * 60),    # Monday 12:30 to 13:00 -> (750,780)
        (15 * 60, 15 * 60 + 30)],   # Monday 15:00 to 15:30 -> (900,930)
    1: [(16 * 60 + 30, 17 * 60)],   # Tuesday 16:30 to 17:00 -> (990,1020)
    2: [(10 * 60, 10 * 60 + 30),    # Wednesday 10:00 to 10:30 -> (600,630)
        (14 * 60 + 30, 15 * 60)],   # Wednesday 14:30 to 15:00 -> (870,900)
    3: [(15 * 60, 15 * 60 + 30),    # Thursday 15:00 to 15:30 -> (900,930)
        (16 * 60, 16 * 60 + 30)]    # Thursday 16:00 to 16:30 -> (960,990)
}

# Busy schedules for Gary.
gary_busy = {
    0: [(9 * 60, 17 * 60)],         # Monday 9:00 to 17:00 -> (540,1020)
    1: [(9 * 60, 10 * 60 + 30),      # Tuesday 9:00 to 10:30 -> (540,630)
        (11 * 60, 11 * 60 + 30),     # Tuesday 11:00 to 11:30 -> (660,690)
        (12 * 60, 17 * 60)],         # Tuesday 12:00 to 17:00 -> (720,1020)
    2: [(9 * 60, 17 * 60)],         # Wednesday 9:00 to 17:00 -> (540,1020)
    3: [(9 * 60, 17 * 60)]          # Thursday 9:00 to 17:00 -> (540,1020)
}

# Utility function to ensure a meeting starting at 's' (with duration 30 mins)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # The meeting start time in minutes from midnight
    
    # Enforce the meeting to finish within the work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Apply Thomas's preference: if the meeting is on Tuesday (day 1),
    # avoid scheduling before 11:30 (i.e. meeting must start at or after 11:30 which is 690 minutes).
    if day == 1:
        solver.add(s >= 11 * 60 + 30)  # 11:30 is 690 minutes.
    
    # Add Thomas's busy intervals for that day.
    for busy_start, busy_end in thomas_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
        
    # Add Gary's busy intervals for that day.
    for busy_start, busy_end in gary_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Try each possible start time (minute by minute) until a valid one is found.
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
    # Convert minutes back to HH:MM string.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")