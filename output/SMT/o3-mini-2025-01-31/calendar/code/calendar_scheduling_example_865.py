from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Days represented as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Megan's busy schedule (times in minutes from midnight)
megan_busy = {
    0: [ (13 * 60, 13 * 60 + 30),    # Monday: 13:00 - 13:30  -> [780,810)
         (14 * 60, 15 * 60 + 30) ],   # Monday: 14:00 - 15:30  -> [840,930)
    1: [ (9 * 60, 9 * 60 + 30),       # Tuesday: 9:00 - 9:30   -> [540,570)
         (12 * 60, 12 * 60 + 30),     # Tuesday: 12:00 - 12:30 -> [720,750)
         (16 * 60, 17 * 60) ],        # Tuesday: 16:00 - 17:00 -> [960,1020)
    2: [ (9 * 60 + 30, 10 * 60),      # Wednesday: 9:30 - 10:00 -> [570,600)
         (10 * 60 + 30, 11 * 60 + 30),# Wednesday: 10:30 - 11:30-> [630,690)
         (12 * 60 + 30, 14 * 60),     # Wednesday: 12:30 - 14:00-> [750,840)
         (16 * 60, 16 * 60 + 30) ],   # Wednesday: 16:00 - 16:30-> [960,990)
    3: [ (13 * 60 + 30, 14 * 60 + 30),# Thursday: 13:30 - 14:30 -> [810,870)
         (15 * 60, 15 * 60 + 30) ]    # Thursday: 15:00 - 15:30 -> [900,930)
}

# Daniel's busy schedule (times in minutes from midnight)
daniel_busy = {
    0: [ (10 * 60, 11 * 60 + 30),     # Monday: 10:00 - 11:30 -> [600,690)
         (12 * 60 + 30, 15 * 60) ],    # Monday: 12:30 - 15:00 -> [750,900)
    1: [ (9 * 60, 10 * 60),           # Tuesday: 9:00 - 10:00  -> [540,600)
         (10 * 60 + 30, 17 * 60) ],    # Tuesday: 10:30 - 17:00 -> [630,1020)
    2: [ (9 * 60, 10 * 60),           # Wednesday: 9:00 - 10:00 -> [540,600)
         (10 * 60 + 30, 11 * 60 + 30), # Wednesday: 10:30 - 11:30-> [630,690)
         (12 * 60, 17 * 60) ],         # Wednesday: 12:00 - 17:00-> [720,1020)
    3: [ (9 * 60, 12 * 60),           # Thursday: 9:00 - 12:00 -> [540,720)
         (12 * 60 + 30, 14 * 60 + 30), # Thursday: 12:30 - 14:30-> [750,870)
         (15 * 60, 15 * 60 + 30),      # Thursday: 15:00 - 15:30-> [900,930)
         (16 * 60, 17 * 60) ]          # Thursday: 16:00 - 17:00-> [960,1020)
}

# Helper function: ensures that the meeting starting at s (lasting duration minutes)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    # Either the meeting ends before the busy interval starts, or starts after it ends.
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest valid meeting time among the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        
        # s represents meeting start time in minutes from midnight
        s = Int("s")
        
        # Meeting must be scheduled within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add constraints for Megan's busy intervals on the given day.
        for interval in megan_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add constraints for Daniel's busy intervals on the given day.
        for interval in daniel_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try all possible start times (minute by minute) for this day.
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
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")