from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration: 30 minutes
WORK_START = 9 * 60     # 9:00 AM in minutes (540)
WORK_END   = 17 * 60    # 17:00 (1020)

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
candidate_days = [0, 1, 2, 3, 4]

# Busy intervals for Daniel (each tuple is (start, end) in minutes)
daniel_busy = {
    0: [(9 * 60 + 30, 10 * 60 + 30),    # Monday: 9:30-10:30
        (12 * 60, 12 * 60 + 30),         # Monday: 12:00-12:30
        (13 * 60, 14 * 60),              # Monday: 13:00-14:00
        (14 * 60 + 30, 15 * 60),         # Monday: 14:30-15:00
        (15 * 60 + 30, 16 * 60)],        # Monday: 15:30-16:00
    1: [(11 * 60, 12 * 60),             # Tuesday: 11:00-12:00
        (13 * 60, 13 * 60 + 30),         # Tuesday: 13:00-13:30
        (15 * 60 + 30, 16 * 60),         # Tuesday: 15:30-16:00
        (16 * 60 + 30, 17 * 60)],        # Tuesday: 16:30-17:00
    2: [(9 * 60, 10 * 60),              # Wednesday: 9:00-10:00
        (14 * 60, 14 * 60 + 30)],        # Wednesday: 14:00-14:30
    3: [(10 * 60 + 30, 11 * 60),         # Thursday: 10:30-11:00
        (12 * 60, 13 * 60),             # Thursday: 12:00-13:00
        (14 * 60 + 30, 15 * 60),         # Thursday: 14:30-15:00
        (15 * 60 + 30, 16 * 60)],        # Thursday: 15:30-16:00
    4: [(9 * 60, 9 * 60 + 30),          # Friday: 9:00-9:30
        (11 * 60 + 30, 12 * 60),         # Friday: 11:30-12:00
        (13 * 60, 13 * 60 + 30),         # Friday: 13:00-13:30
        (16 * 60 + 30, 17 * 60)]         # Friday: 16:30-17:00
}

# Busy intervals for Bradley
bradley_busy = {
    0: [(9 * 60 + 30, 11 * 60),         # Monday: 9:30-11:00
        (11 * 60 + 30, 12 * 60),         # Monday: 11:30-12:00
        (12 * 60 + 30, 13 * 60),         # Monday: 12:30-13:00
        (14 * 60, 15 * 60)],             # Monday: 14:00-15:00
    1: [(10 * 60 + 30, 11 * 60),         # Tuesday: 10:30-11:00
        (12 * 60, 13 * 60),             # Tuesday: 12:00-13:00
        (13 * 60 + 30, 14 * 60),         # Tuesday: 13:30-14:00
        (15 * 60 + 30, 16 * 60 + 30)],    # Tuesday: 15:30-16:30
    2: [(9 * 60, 10 * 60),              # Wednesday: 9:00-10:00
        (11 * 60, 13 * 60),             # Wednesday: 11:00-13:00
        (13 * 60 + 30, 14 * 60),         # Wednesday: 13:30-14:00
        (14 * 60 + 30, 17 * 60)],        # Wednesday: 14:30-17:00
    3: [(9 * 60, 12 * 60 + 30),         # Thursday: 9:00-12:30
        (13 * 60 + 30, 14 * 60),         # Thursday: 13:30-14:00
        (14 * 60 + 30, 15 * 60),         # Thursday: 14:30-15:00
        (15 * 60 + 30, 16 * 60 + 30)],    # Thursday: 15:30-16:30
    4: [(9 * 60, 9 * 60 + 30),          # Friday: 9:00-9:30
        (10 * 60, 12 * 60 + 30),         # Friday: 10:00-12:30
        (13 * 60, 13 * 60 + 30),         # Friday: 13:00-13:30
        (14 * 60, 14 * 60 + 30),         # Friday: 14:00-14:30
        (15 * 60 + 30, 16 * 60 + 30)]     # Friday: 15:30-16:30
}

# Preferences:
# Daniel prefers NOT to meet on Wednesday (2) or Thursday (3).
# Bradley does not want to meet on Monday (0) or Friday (4).
# Also, Bradley does not want meetings on Tuesday that start before 12:00 (i.e. before 720 minutes).

def no_overlap(busy_start, busy_end, s, duration):
    # returns a constraint that a meeting starting at s (lasting duration) 
    # does not overlap with busy interval [busy_start, busy_end)
    return Or(s + duration <= busy_start, s >= busy_end)

def find_meeting_time(days):
    # Iterate over candidate days
    for day in days:
        # Apply preference constraints for days:
        # Daniel does not want Wednesday (2) or Thursday (3)
        if day in [2, 3]:
            continue
        # Bradley does not want Monday (0) or Friday (4)
        if day in [0, 4]:
            continue
        
        # If we've reached here, day must be Tuesday (day == 1)
        solver = Solver()
        
        # Meeting start time (in minutes after midnight)
        s = Int("s")
        # Basic working hours constraint
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Additional Bradley preference for Tuesday: meeting must not start before 12:00 (720 minutes)
        if day == 1:
            solver.add(s >= 12 * 60)
        
        # Add Daniel's busy interval constraints (if any on this day)
        if day in daniel_busy:
            for busy_start, busy_end in daniel_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Bradley's busy interval constraints (if any on this day)
        if day in bradley_busy:
            for busy_start, busy_end in bradley_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Try every possible minute in the allowed window for a valid solution.
        # We iterate from max(WORK_START, possible preference lower bound) to WORK_END - duration.
        start_min_candidate = 12 * 60 if day == 1 else WORK_START
        for t in range(start_min_candidate, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None and t is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")