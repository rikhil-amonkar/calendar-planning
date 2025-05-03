from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Days represented as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Betty cannot meet on Monday.
# Betty also cannot meet on Tuesday and Thursday before 15:00.
# Scott would prefer to avoid Wednesday.
# Hence, we try Tuesday, then Thursday, and fall back to Wednesday if needed.
candidate_days = [1, 3, 2]

# Betty's busy schedule (times in minutes from midnight)
betty_busy = {
    0: [ (10 * 60, 10 * 60 + 30),   # Monday: 10:00-10:30  -> [600,630)
         (13 * 60 + 30, 14 * 60),   # Monday: 13:30-14:00  -> [810,840)
         (15 * 60, 15 * 60 + 30),   # Monday: 15:00-15:30  -> [900,930)
         (16 * 60, 16 * 60 + 30) ], # Monday: 16:00-16:30  -> [960,990)
    1: [ (9 * 60, 9 * 60 + 30),     # Tuesday: 9:00-9:30   -> [540,570)
         (11 * 60 + 30, 12 * 60),   # Tuesday: 11:30-12:00 -> [690,720)
         (12 * 60 + 30, 13 * 60),   # Tuesday: 12:30-13:00 -> [750,780)
         (13 * 60 + 30, 14 * 60),   # Tuesday: 13:30-14:00 -> [810,840)
         (16 * 60 + 30, 17 * 60) ], # Tuesday: 16:30-17:00 -> [990,1020)
    2: [ (9 * 60 + 30, 10 * 60 + 30),   # Wednesday: 9:30-10:30 -> [570,630)
         (13 * 60, 13 * 60 + 30),       # Wednesday: 13:00-13:30 -> [780,810)
         (14 * 60, 14 * 60 + 30) ],      # Wednesday: 14:00-14:30 -> [840,870)
    3: [ (9 * 60 + 30, 10 * 60),     # Thursday: 9:30-10:00  -> [570,600)
         (11 * 60 + 30, 12 * 60),    # Thursday: 11:30-12:00 -> [690,720)
         (14 * 60, 14 * 60 + 30),    # Thursday: 14:00-14:30 -> [840,870)
         (15 * 60, 15 * 60 + 30),    # Thursday: 15:00-15:30 -> [900,930)
         (16 * 60 + 30, 17 * 60) ]   # Thursday: 16:30-17:00 -> [990,1020)
}

# Scott's busy schedule (times in minutes from midnight)
scott_busy = {
    0: [ (9 * 60 + 30, 15 * 60),    # Monday: 9:30-15:00 -> [570,900)
         (15 * 60 + 30, 16 * 60),    # Monday: 15:30-16:00 -> [930,960)
         (16 * 60 + 30, 17 * 60) ],  # Monday: 16:30-17:00 -> [990,1020)
    1: [ (9 * 60, 9 * 60 + 30),      # Tuesday: 9:00-9:30  -> [540,570)
         (10 * 60, 11 * 60),         # Tuesday: 10:00-11:00-> [600,660)
         (11 * 60 + 30, 12 * 60),     # Tuesday: 11:30-12:00-> [690,720)
         (12 * 60 + 30, 13 * 60 + 30),# Tuesday: 12:30-13:30-> [750,810)
         (14 * 60, 15 * 60),         # Tuesday: 14:00-15:00-> [840,900)
         (16 * 60, 16 * 60 + 30) ],   # Tuesday: 16:00-16:30-> [960,990)
    2: [ (9 * 60 + 30, 12 * 60 + 30), # Wednesday: 9:30-12:30-> [570,750)
         (13 * 60, 13 * 60 + 30),     # Wednesday: 13:00-13:30-> [780,810)
         (14 * 60, 14 * 60 + 30),     # Wednesday: 14:00-14:30-> [840,870)
         (15 * 60, 15 * 60 + 30),     # Wednesday: 15:00-15:30-> [900,930)
         (16 * 60, 16 * 60 + 30) ],   # Wednesday: 16:00-16:30-> [960,990)
    3: [ (9 * 60, 9 * 60 + 30),      # Thursday: 9:00-9:30   -> [540,570)
         (10 * 60, 10 * 60 + 30),    # Thursday: 10:00-10:30 -> [600,630)
         (11 * 60, 12 * 60),         # Thursday: 11:00-12:00 -> [660,720)
         (12 * 60 + 30, 13 * 60),    # Thursday: 12:30-13:00 -> [750,780)
         (15 * 60, 16 * 60),         # Thursday: 15:00-16:00 -> [900,960)
         (16 * 60 + 30, 17 * 60) ]    # Thursday: 16:30-17:00 -> [990,1020)
}

# Helper function: ensures that a meeting starting at s (lasting duration minutes)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# This function searches for the earliest available meeting time on a given candidate day.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        
        # Meeting must be scheduled within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Apply Betty's preference: on Tuesday (day==1) and Thursday (day==3), meeting must start at or after 15:00 (900 minutes)
        if day in [1, 3]:
            solver.add(s >= 15 * 60)  # 15:00 is 900 minutes
        
        # Add Betty's busy schedule constraints for the day.
        for interval in betty_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Scott's busy schedule constraints for the day.
        for interval in scott_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Determine the starting minute for search:
        # If day is Tuesday or Thursday, start from max(WORK_START, 15:00), otherwise from WORK_START.
        search_start = max(WORK_START, 15 * 60) if day in [1, 3] else WORK_START
        
        # Search minute-by-minute over possible start times within work hours.
        for t in range(search_start, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

if selected_day is not None:
    selected_end = selected_start + duration
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".
          format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")