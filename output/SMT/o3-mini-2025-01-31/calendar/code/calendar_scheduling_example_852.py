from z3 import Solver, Int, Or, sat

# Meeting duration in minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Define days as follows:
# Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Given the constraints:
# - Randy does not want to meet on Monday.
# - Maria would rather not meet on Wednesday after 13:30.
#
# Also note from the busy schedules, Tuesday is fully busy for Maria.
# Thus our candidate days will be Wednesday (2) and Thursday (3).
candidate_days = [2, 3]

# Busy intervals for Randy, expressed in minutes from midnight.
randy_busy = {
    0: [(10*60, 10*60+30),       # Monday 10:00 to 10:30  -> (600,630)
        (11*60, 11*60+30),       # Monday 11:00 to 11:30  -> (660,690)
        (12*60, 13*60),          # Monday 12:00 to 13:00  -> (720,780)
        (13*60+30, 14*60+30),     # Monday 13:30 to 14:30  -> (810,870)
        (16*60, 16*60+30)],      # Monday 16:00 to 16:30  -> (960,990)
    1: [(10*60, 11*60+30),       # Tuesday 10:00 to 11:30 -> (600,690)
        (12*60+30, 13*60),       # Tuesday 12:30 to 13:00 -> (750,780)
        (15*60, 15*60+30),       # Tuesday 15:00 to 15:30 -> (900,930)
        (16*60, 17*60)],        # Tuesday 16:00 to 17:00 -> (960,1020)
    2: [(10*60+30, 11*60),       # Wednesday 10:30 to 11:00 -> (630,660)
        (11*60+30, 12*60),       # Wednesday 11:30 to 12:00 -> (690,720)
        (13*60, 13*60+30),       # Wednesday 13:00 to 13:30 -> (780,810)
        (15*60+30, 16*60)],      # Wednesday 15:30 to 16:00 -> (930,960)
    3: [(9*60+30, 10*60),        # Thursday 9:30 to 10:00  -> (570,600)
        (10*60+30, 11*60),       # Thursday 10:30 to 11:00 -> (630,660)
        (12*60, 13*60+30),       # Thursday 12:00 to 13:30 -> (720,810)
        (16*60+30, 17*60)]       # Thursday 16:30 to 17:00 -> (990,1020)
}

# Busy intervals for Maria
maria_busy = {
    0: [(9*60, 10*60),          # Monday 9:00 to 10:00   -> (540,600)
        (11*60, 13*60+30),       # Monday 11:00 to 13:30  -> (660,810)
        (14*60, 14*60+30),       # Monday 14:00 to 14:30  -> (840,870)
        (15*60, 15*60+30),       # Monday 15:00 to 15:30  -> (900,930)
        (16*60, 17*60)],        # Monday 16:00 to 17:00  -> (960,1020)
    1: [(9*60, 17*60)],         # Tuesday 9:00 to 17:00  -> (540,1020)
    2: [(9*60+30, 10*60),       # Wednesday 9:30 to 10:00 -> (570,600)
        (10*60+30, 12*60),       # Wednesday 10:30 to 12:00-> (630,720)
        (14*60+30, 15*60+30),     # Wednesday 14:30 to 15:30-> (870,930)
        (16*60, 17*60)],        # Wednesday 16:00 to 17:00-> (960,1020)
    3: [(9*60+30, 10*60),        # Thursday 9:30 to 10:00  -> (570,600)
        (11*60+30, 12*60+30),     # Thursday 11:30 to 12:30 -> (690,750)
        (13*60+30, 15*60),        # Thursday 13:30 to 15:00 -> (810,900)
        (16*60+30, 17*60)]        # Thursday 16:30 to 17:00 -> (990,1020)
}

# Utility function to ensure that a meeting starting at time 's' (lasting `duration` minutes)
# does not overlap with a busy interval given by [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

for day in candidate_days:
    solver = Solver()
    s = Int("s")  # Meeting start time in minutes from midnight
    
    # Ensure the meeting is scheduled within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Apply additional day-based preferences.
    # If the meeting is scheduled on Wednesday (day == 2),
    # Maria prefers not to have it after 13:30.
    # Since the meeting lasts 30 minutes, enforce: s + duration <= 13:30 (i.e. 810 minutes)
    if day == 2:
        solver.add(s + duration <= 13 * 60 + 30)  # s <= 810 - 30, i.e. s <= 780
    
    # Add busy constraints for Randy.
    for busy_start, busy_end in randy_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
        
    # Add busy constraints for Maria.
    for busy_start, busy_end in maria_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Try possible start times (minute by minute) within the work hours.
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
    # Convert minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")