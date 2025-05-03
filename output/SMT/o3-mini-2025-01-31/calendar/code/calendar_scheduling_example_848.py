from z3 import Solver, Int, Or, sat

# Meeting duration is 30 minutes.
duration = 30

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes).
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# Days are encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Given the participant preferences:
# - Larry does not want to meet on Monday.
# - Kenneth cannot meet on Tuesday.
# Therefore, we only consider Wednesday (2) and Thursday (3).
candidate_days = [2, 3]

# Larry's busy schedule (times in minutes from midnight):
# Monday:
#   9:30-10:00 -> (570,600), 10:30-11:30 -> (630,690),
#   14:00-14:30 -> (840,870), 15:00-15:30 -> (900,930), 
#   16:00-16:30 -> (960,990)
#
# Tuesday:
#   9:30-10:30 -> (570,630), 11:00-11:30 -> (660,690),
#   13:00-14:00 -> (780,840), 15:00-16:00 -> (900,960),
#   16:30-17:00 -> (990,1020)
#
# Wednesday:
#   10:00-11:00 -> (600,660), 11:30-12:00 -> (690,720),
#   15:00-15:30 -> (900,930)
#
# Thursday:
#   9:30-12:30 -> (570,750), 13:00-14:00 -> (780,840),
#   14:30-15:00 -> (870,900), 15:30-17:00 -> (930,1020)
larry_busy = {
    0: [(570,600), (630,690), (840,870), (900,930), (960,990)],
    1: [(570,630), (660,690), (780,840), (900,960), (990,1020)],
    2: [(600,660), (690,720), (900,930)],
    3: [(570,750), (780,840), (870,900), (930,1020)]
}

# Kenneth's busy schedule:
# Monday:
#   9:00-11:30 -> (540,690), 12:00-17:00 -> (720,1020)
#
# Tuesday:
#   9:00-10:00 -> (540,600), 12:00-14:00 -> (720,840),
#   14:30-16:30 -> (870,990)
#
# Wednesday:
#   9:00-10:00 -> (540,600), 11:30-14:00 -> (690,840),
#   14:30-15:30 -> (870,930), 16:00-17:00 -> (960,1020)
#
# Thursday:
#   9:00-17:00 -> (540,1020)
kenneth_busy = {
    0: [(540,690), (720,1020)],
    1: [(540,600), (720,840), (870,990)],
    2: [(540,600), (690,840), (870,930), (960,1020)],
    3: [(540,1020)]
}

# Additional participant preferences:
# - Larry does not want to meet on Monday (handled by candidate_days).
# - Kenneth cannot meet on Tuesday (handled by candidate_days).
# - Larry does not want to meet on Wednesday after 13:00,
#   so on Wednesday (day==2) the meeting must finish by 13:00 (i.e. s + duration <= 780).
    
# Utility function to ensure a meeting starting at s (lasting duration minutes)
# does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

solution_found = False
selected_day = None
selected_start = None

for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time in minutes since midnight
    
    # Meeting must be within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add extra constraint: if the meeting is on Wednesday, Larry does not want to meet after 13:00.
    if day == 2:  # Wednesday
        solver.add(s + duration <= 13 * 60)  # must finish by 13:00 (780 minutes)
    
    # Add Larry's busy intervals as constraints.
    for (busy_start, busy_end) in larry_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Add Kenneth's busy intervals as constraints.
    for (busy_start, busy_end) in kenneth_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, s))
    
    # Search for the earliest valid start time within the workday for this day.
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
    # Convert time in minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")