from z3 import Solver, Int, Or, sat

# Meeting parameters.
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 AM in minutes (540)
WORK_END   = 17 * 60  # 17:00 in minutes (1020)

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Existing busy intervals.
# Each interval is represented as a tuple (start, end) where times are in minutes from midnight.
# Busy intervals are assumed non-overlapping and given in half-open intervals [start, end).

# Sharon's busy intervals.
sharon_busy = {
    0: [(9 * 60 + 30, 10 * 60)],    # Monday: 9:30-10:00
    2: [(12 * 60, 12 * 60 + 30)],     # Wednesday: 12:00-12:30
    4: [(10 * 60 + 30, 11 * 60)]      # Friday: 10:30-11:00
}

# Martha's busy intervals.
martha_busy = {
    0: [(10 * 60, 10 * 60 + 30),      # Monday: 10:00-10:30
        (11 * 60 + 30, 12 * 60),      # Monday: 11:30-12:00
        (13 * 60 + 30, 14 * 60),      # Monday: 13:30-14:00
        (15 * 60, 15 * 60 + 30)],     # Monday: 15:00-15:30
    1: [(9 * 60, 10 * 60 + 30),       # Tuesday: 9:00-10:30
        (11 * 60 + 30, 13 * 60 + 30),  # Tuesday: 11:30-13:30
        (14 * 60, 16 * 60)],          # Tuesday: 14:00-16:00
    2: [(9 * 60, 9 * 60 + 30),        # Wednesday: 9:00-9:30
        (10 * 60, 15 * 60),          # Wednesday: 10:00-15:00
        (15 * 60 + 30, 16 * 60 + 30)], # Wednesday: 15:30-16:30
    3: [(10 * 60, 11 * 60 + 30),      # Thursday: 10:00-11:30
        (12 * 60, 13 * 60 + 30),      # Thursday: 12:00-13:30
        (14 * 60, 16 * 60 + 30)],     # Thursday: 14:00-16:30
    4: [(9 * 60 + 30, 11 * 60),       # Friday: 9:30-11:00
        (11 * 60 + 30, 15 * 60 + 30),  # Friday: 11:30-15:30
        (16 * 60, 17 * 60)]           # Friday: 16:00-17:00
}

# Preferences:
# Sharon would like to avoid more meetings on Monday and Tuesday.
# (These are soft constraints so we try to schedule on other days first.)
#
# We'll try to schedule the meeting on a "preferred" day (Wednesday, Thursday, Friday)
# and only if no solution is found there, we will consider Monday and Tuesday.

preferred_days = [2, 3, 4]  # Wednesday, Thursday, Friday (in that order)
backup_days    = [0, 1]     # Monday, Tuesday

def no_overlap(busy_start, busy_end, s, duration):
    # Returns a constraint ensuring that the meeting (from s to s+duration)
    # does not overlap with the busy interval [busy_start, busy_end).
    return Or(s + duration <= busy_start, s >= busy_end)

def find_meeting_time(candidate_days):
    for day in candidate_days:
        solver = Solver()
        # Define integer variable for meeting start time (in minutes).
        s = Int("s")
        # The meeting must be scheduled within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Sharon's busy intervals constraints.
        if day in sharon_busy:
            for start_busy, end_busy in sharon_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
                
        # Add Martha's busy intervals constraints.
        if day in martha_busy:
            for start_busy, end_busy in martha_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
                
        # Try every possible minute start in the working window.
        # (We iterate over possible start times because time is represented in minutes.)
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# First attempt: try preferred days (avoid Monday and Tuesday per Sharon's preference).
day, t = find_meeting_time(preferred_days)

# If no valid meeting time is found on the preferred days, try backup days.
if day is None:
    day, t = find_meeting_time(backup_days)
    
if day is not None and t is not None:
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".
          format(day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")