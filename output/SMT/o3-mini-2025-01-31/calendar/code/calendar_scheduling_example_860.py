from z3 import Solver, Int, Or, sat

# Meeting duration: 1 hour = 60 minutes
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# The group would like to meet at their earliest availability, so we check days in order.
candidate_days = [0, 1, 2, 3]

# Busy schedules for Mark (times in minutes from midnight).
mark_busy = {
    0: [],  # Monday: no busy intervals
    1: [],  # Tuesday: no busy intervals
    2: [ (14 * 60, 14 * 60 + 30) ],  # Wednesday: 14:00-14:30
    3: [ (14 * 60 + 30, 15 * 60) ]   # Thursday: 14:30-15:00
}

# Busy schedules for Helen (times in minutes from midnight).
helen_busy = {
    0: [ (10 * 60, 10 * 60 + 30),    # Monday: 10:00-10:30
         (11 * 60 + 30, 14 * 60 + 30) ],  # Monday: 11:30-14:30
    1: [ (9 * 60, 10 * 60),          # Tuesday: 9:00-10:00
         (10 * 60 + 30, 11 * 60),     # Tuesday: 10:30-11:00
         (11 * 60 + 30, 12 * 60),     # Tuesday: 11:30-12:00
         (12 * 60 + 30, 13 * 60 + 30),# Tuesday: 12:30-13:30
         (14 * 60 + 30, 15 * 60),     # Tuesday: 14:30-15:00
         (16 * 60, 16 * 60 + 30) ],   # Tuesday: 16:00-16:30
    2: [ (9 * 60, 9 * 60 + 30),      # Wednesday: 9:00-9:30
         (10 * 60, 12 * 60),         # Wednesday: 10:00-12:00
         (13 * 60 + 30, 15 * 60),     # Wednesday: 13:30-15:00
         (15 * 60 + 30, 16 * 60) ],   # Wednesday: 15:30-16:00
    3: [ (10 * 60, 10 * 60 + 30),     # Thursday: 10:00-10:30
         (13 * 60, 14 * 60 + 30),     # Thursday: 13:00-14:30
         (15 * 60, 17 * 60) ]         # Thursday: 15:00-17:00
}

# Helper function: Given a busy interval [busy_start, busy_end) and meeting start s (of fixed duration)
# returns a constraint ensuring the meeting does NOT overlap with the busy interval.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to try all candidate days and return the earliest available meeting time.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # The meeting must lie within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Mark's busy intervals for the current day.
        for interval in mark_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Helen's busy intervals for the current day.
        for interval in helen_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try all possible start times (from WORK_START to last possible start time).
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
    # Convert the start and end times to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")