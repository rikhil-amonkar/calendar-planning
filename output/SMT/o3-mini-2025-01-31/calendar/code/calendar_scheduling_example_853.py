from z3 import Solver, Int, Or, sat

# Meeting duration in minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# James does not want to meet on Tuesday so we exclude day 1.
candidate_days = [0, 2, 3]

# Busy intervals for James (times in minutes from midnight)
james_busy = {
    0: [(9*60, 10*60),         # Monday: 09:00 to 10:00 -> (540,600)
        (11*60+30, 12*60),      # Monday: 11:30 to 12:00 -> (690,720)
        (13*60, 15*60),         # Monday: 13:00 to 15:00 -> (780,900)
        (15*60+30, 16*60+30)],   # Monday: 15:30 to 16:30 -> (930,990)
    1: [(13*60, 13*60+30),      # Tuesday: 13:00 to 13:30 -> (780,810)
        (14*60, 14*60+30)],     # Tuesday: 14:00 to 14:30 -> (840,870)
    2: [(9*60+30, 10*60+30),    # Wednesday: 09:30 to 10:30 -> (570,630)
        (11*60, 14*60),         # Wednesday: 11:00 to 14:00 -> (660,840)
        (15*60, 15*60+30),       # Wednesday: 15:00 to 15:30 -> (900,930)
        (16*60+30, 17*60)],      # Wednesday: 16:30 to 17:00 -> (990,1020)
    3: [(10*60, 10*60+30),      # Thursday: 10:00 to 10:30 -> (600,630)
        (11*60, 12*60),         # Thursday: 11:00 to 12:00 -> (660,720)
        (14*60, 15*60),         # Thursday: 14:00 to 15:00 -> (840,900)
        (15*60+30, 16*60),       # Thursday: 15:30 to 16:00 -> (930,960)
        (16*60+30, 17*60)]       # Thursday: 16:30 to 17:00 -> (990,1020)
}

# Busy intervals for Gabriel (times in minutes from midnight)
gabriel_busy = {
    0: [(9*60, 14*60+30),      # Monday: 09:00 to 14:30 -> (540,870)
        (15*60, 17*60)],       # Monday: 15:00 to 17:00 -> (900,1020)
    1: [(9*60, 15*60),         # Tuesday: 09:00 to 15:00 -> (540,900)
        (15*60+30, 17*60)],     # Tuesday: 15:30 to 17:00 -> (930,1020)
    2: [(9*60, 17*60)],        # Wednesday: 09:00 to 17:00 -> (540,1020)
    3: [(9*60+30, 13*60+30),    # Thursday: 09:30 to 13:30 -> (570,810)
        (14*60, 17*60)]        # Thursday: 14:00 to 17:00 -> (840,1020)
}

# Utility function: meeting starting at time 's' must not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes from midnight
    
    # Meeting must be within working hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Additional day-specific constraints:
    # Gabriel prefers not to meet on Thursday before 11:00.
    if day == 3:
        solver.add(s >= 11 * 60)  # meeting cannot start before 11:00

    # Add James's busy constraints for the day.
    for busy_start, busy_end in james_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add Gabriel's busy constraints for the day.
    for busy_start, busy_end in gabriel_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Try possible start times (minute by minute) within [WORK_START, WORK_END-duration]
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
    # Convert minutes into HH:MM.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
            .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")