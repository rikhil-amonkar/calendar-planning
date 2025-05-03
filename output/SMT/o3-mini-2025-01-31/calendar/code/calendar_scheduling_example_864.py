from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # in minutes, meeting duration is 1 hour
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END   = 17 * 60  # 17:00 in minutes (1020)

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Bruce would rather not meet on Wednesday. Hence we search Monday, Tuesday, and Thursday first.
candidate_days = [0, 1, 3]

# Bruce's busy schedule (times as minutes from midnight)
bruce_busy = {
    0: [ (9 * 60, 9 * 60 + 30),       # Monday: 9:00-9:30 -> [540,570)
         (10 * 60 + 30, 11 * 60),     # Monday: 10:30-11:00 -> [630,660)
         (12 * 60, 12 * 60 + 30),     # Monday: 12:00-12:30 -> [720,750)
         (13 * 60, 13 * 60 + 30),     # Monday: 13:00-13:30 -> [780,810)
         (14 * 60, 14 * 60 + 30),     # Monday: 14:00-14:30 -> [840,870)
         (16 * 60, 16 * 60 + 30) ],   # Monday: 16:00-16:30 -> [960,990)
    1: [ (10 * 60, 10 * 60 + 30),     # Tuesday: 10:00-10:30 -> [600,630)
         (12 * 60 + 30, 13 * 60 + 30), # Tuesday: 12:30-13:30 -> [750,810)
         (16 * 60 + 30, 17 * 60) ],    # Tuesday: 16:30-17:00 -> [990,1020)
    2: [ (10 * 60, 10 * 60 + 30),     # Wednesday: 10:00-10:30 -> [600,630)
         (12 * 60, 12 * 60 + 30),     # Wednesday: 12:00-12:30 -> [720,750)
         (15 * 60, 15 * 60 + 30) ],    # Wednesday: 15:00-15:30 -> [900,930)
    3: [ (11 * 60 + 30, 12 * 60 + 30), # Thursday: 11:30-12:30 -> [690,750)
         (14 * 60 + 30, 15 * 60) ]     # Thursday: 14:30-15:00 -> [870,900)
}

# Amy's busy schedule (times as minutes from midnight)
amy_busy = {
    0: [ (9 * 60, 10 * 60),          # Monday: 9:00-10:00 -> [540,600)
         (11 * 60, 11 * 60 + 30),    # Monday: 11:00-11:30 -> [660,690)
         (13 * 60 + 30, 14 * 60),    # Monday: 13:30-14:00 -> [810,840)
         (14 * 60 + 30, 15 * 60 + 30),# Monday: 14:30-15:30 -> [870,930)
         (16 * 60, 17 * 60) ],       # Monday: 16:00-17:00 -> [960,1020)
    1: [ (9 * 60, 14 * 60),          # Tuesday: 9:00-14:00 -> [540,840)
         (15 * 60 + 30, 16 * 60) ],   # Tuesday: 15:30-16:00 -> [930,960)
    2: [ (9 * 60, 9 * 60 + 30),       # Wednesday: 9:00-9:30 -> [540,570)
         (10 * 60, 13 * 60),         # Wednesday: 10:00-13:00 -> [600,780)
         (13 * 60 + 30, 14 * 60),     # Wednesday: 13:30-14:00 -> [810,840)
         (14 * 60 + 30, 15 * 60 + 30), # Wednesday: 14:30-15:30 -> [870,930)
         (16 * 60 + 30, 17 * 60) ],   # Wednesday: 16:30-17:00 -> [990,1020)
    3: [ (9 * 60, 10 * 60),          # Thursday: 9:00-10:00 -> [540,600)
         (10 * 60 + 30, 12 * 60),     # Thursday: 10:30-12:00 -> [630,720)
         (12 * 60 + 30, 13 * 60),     # Thursday: 12:30-13:00 -> [750,780)
         (13 * 60 + 30, 14 * 60),     # Thursday: 13:30-14:00 -> [810,840)
         (15 * 60, 16 * 60 + 30) ]     # Thursday: 15:00-16:30 -> [900,990)
}

# Helper function: Ensure meeting [s, s+duration) does not overlap with a busy interval.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find earliest valid meeting time among candidate days
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        
        # The meeting must be within work hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Bruce's busy time constraints for the day
        for interval in bruce_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Amy's busy time constraints for the day
        for interval in amy_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Search minute-by-minute over possible start times
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

if selected_day is not None:
    selected_end = selected_start + duration
    # Convert minutes into HH:MM strings.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")