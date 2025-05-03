from z3 import Solver, Int, Or, sat

# Meeting duration (30 minutes)
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Preferences:
# • Randy would rather not meet on Tuesday.
# • George would like to avoid more meetings on Thursday.
# Therefore, we order the candidate days to first check Monday and Wednesday,
# then Tuesday, and finally Thursday.
candidate_days = [0, 2, 1, 3]

# Busy schedules for Randy (times in minutes from midnight).
randy_busy = {
    0: [],                # Monday: no meetings
    1: [],                # Tuesday: no meetings (but Randy prefers to avoid Tuesday)
    2: [ (12 * 60, 12 * 60 + 30),   # Wednesday: 12:00-12:30
         (14 * 60 + 30, 15 * 60) ],  # Wednesday: 14:30-15:00
    3: []                 # Thursday: no meetings
}

# Busy schedules for George (times in minutes from midnight).
george_busy = {
    0: [ (9 * 60 + 30, 10 * 60),    # Monday: 9:30-10:00
         (11 * 60, 12 * 60),        # Monday: 11:00-12:00
         (12 * 60 + 30, 13 * 60),   # Monday: 12:30-13:00
         (14 * 60, 17 * 60) ],      # Monday: 14:00-17:00
    1: [ (9 * 60, 9 * 60 + 30),     # Tuesday: 9:00-9:30
         (10 * 60, 10 * 60 + 30),   # Tuesday: 10:00-10:30
         (11 * 60, 14 * 60),        # Tuesday: 11:00-14:00
         (14 * 60 + 30, 17 * 60) ],  # Tuesday: 14:30-17:00
    2: [ (9 * 60, 11 * 60),         # Wednesday: 9:00-11:00
         (12 * 60, 12 * 60 + 30),   # Wednesday: 12:00-12:30
         (13 * 60, 15 * 60),        # Wednesday: 13:00-15:00
         (16 * 60, 16 * 60 + 30) ],  # Wednesday: 16:00-16:30
    3: [ (10 * 60, 11 * 60),        # Thursday: 10:00-11:00
         (11 * 60 + 30, 12 * 60 + 30), # Thursday: 11:30-12:30
         (13 * 60 + 30, 14 * 60),    # Thursday: 13:30-14:00
         (15 * 60, 15 * 60 + 30),    # Thursday: 15:00-15:30
         (16 * 60, 16 * 60 + 30) ]   # Thursday: 16:00-16:30
}

# Helper function to ensure a meeting starting at time s (with fixed duration)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time on one of the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        
        # The meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add constraints for Randy's busy intervals on this day.
        for busy_start, busy_end in randy_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # Add constraints for George's busy intervals on this day.
        for busy_start, busy_end in george_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # We look for the earliest possible start time within work hours.
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
    # Convert minutes into HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")