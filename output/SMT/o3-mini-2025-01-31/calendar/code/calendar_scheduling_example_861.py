from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Amber would like to avoid more meetings on Thursday, so we try Monday, Tuesday, and Wednesday first.
preferred_days = [0, 1, 2]
other_days = [3]
candidate_days = preferred_days + other_days  # try Thursday only if needed

# Busy schedules for Amber (times in minutes from midnight).
amber_busy = {
    0: [ (11 * 60, 11 * 60 + 30),    # Monday: 11:00-11:30
         (12 * 60, 13 * 60 + 30),    # Monday: 12:00-13:30
         (14 * 60, 14 * 60 + 30) ],  # Monday: 14:00-14:30
    1: [ (10 * 60, 11 * 60),         # Tuesday: 10:00-11:00
         (14 * 60, 14 * 60 + 30) ],   # Tuesday: 14:00-14:30
    2: [ (9 * 60, 9 * 60 + 30),       # Wednesday: 9:00-9:30
         (10 * 60, 10 * 60 + 30),     # Wednesday: 10:00-10:30
         (12 * 60, 13 * 60),          # Wednesday: 12:00-13:00
         (14 * 60, 15 * 60 + 30),     # Wednesday: 14:00-15:30
         (16 * 60, 16 * 60 + 30) ],   # Wednesday: 16:00-16:30
    3: [ (9 * 60 + 30, 10 * 60 + 30),  # Thursday: 9:30-10:30
         (11 * 60, 11 * 60 + 30),      # Thursday: 11:00-11:30
         (12 * 60 + 30, 13 * 60),      # Thursday: 12:30-13:00
         (14 * 60, 15 * 60),           # Thursday: 14:00-15:00
         (15 * 60 + 30, 16 * 60 + 30) ] # Thursday: 15:30-16:30
}

# Busy schedules for Raymond (times in minutes from midnight).
raymond_busy = {
    0: [ (9 * 60, 9 * 60 + 30),      # Monday: 9:00-9:30
         (10 * 60, 10 * 60 + 30),    # Monday: 10:00-10:30
         (11 * 60, 11 * 60 + 30),    # Monday: 11:00-11:30
         (12 * 60, 17 * 60) ],       # Monday: 12:00-17:00
    1: [ (9 * 60, 12 * 60),         # Tuesday: 9:00-12:00
         (12 * 60 + 30, 17 * 60) ],  # Tuesday: 12:30-17:00
    2: [ (9 * 60, 10 * 60 + 30),     # Wednesday: 9:00-10:30
         (11 * 60, 11 * 60 + 30),    # Wednesday: 11:00-11:30
         (12 * 60, 12 * 60 + 30),    # Wednesday: 12:00-12:30
         (13 * 60, 17 * 60) ],       # Wednesday: 13:00-17:00
    3: [ (9 * 60, 13 * 60),         # Thursday: 9:00-13:00
         (13 * 60 + 30, 17 * 60) ]   # Thursday: 13:30-17:00
}

# Helper function to ensure meeting does NOT overlap a busy interval.
def no_overlap(busy_start, busy_end, s):
    # Meeting [s, s+duration) should be completely before the busy interval or start after it ends.
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time for a given set of candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # The meeting must fit within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Amber's busy constraints for the day.
        for busy_interval in amber_busy.get(day, []):
            busy_start, busy_end = busy_interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Raymond's busy constraints for the day.
        for busy_interval in raymond_busy.get(day, []):
            busy_start, busy_end = busy_interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try every possible start time (minute by minute) from WORK_START to the last valid start moment.
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
    # Format the start and end times as HH:MM.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")