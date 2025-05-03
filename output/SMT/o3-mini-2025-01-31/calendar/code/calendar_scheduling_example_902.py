from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # 60 minutes meeting duration
WORK_START = 9 * 60     # 9:00 in minutes (540)
WORK_END = 17 * 60      # 17:00 in minutes (1020)

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
candidate_days = [0, 1, 2, 3, 4]

# Lawrence's busy intervals (in minutes from midnight)
lawrence_busy = {
    0: [(9 * 60 + 30, 10 * 60),   # Monday: 9:30-10:00
        (10 * 60 + 30, 11 * 60),  # 10:30-11:00
        (15 * 60 + 30, 16 * 60)], # 15:30-16:00
    1: [(9 * 60, 9 * 60 + 30),    # Tuesday: 9:00-9:30
        (10 * 60, 11 * 60),       # 10:00-11:00
        (11 * 60 + 30, 12 * 60),  # 11:30-12:00
        (13 * 60 + 30, 14 * 60)], # 13:30-14:00
    2: [(9 * 60, 9 * 60 + 30),    # Wednesday: 9:00-9:30
        (10 * 60, 10 * 60 + 30),  # 10:00-10:30
        (11 * 60, 11 * 60 + 30),  # 11:00-11:30
        (13 * 60, 13 * 60 + 30),  # 13:00-13:30
        (15 * 60, 16 * 60),       # 15:00-16:00
        (16 * 60 + 30, 17 * 60)], # 16:30-17:00
    3: [(9 * 60, 9 * 60 + 30),    # Thursday: 9:00-9:30
        (11 * 60, 12 * 60 + 30),  # 11:00-12:30
        (13 * 60 + 30, 14 * 60),  # 13:30-14:00
        (16 * 60, 16 * 60 + 30)], # 16:00-16:30
    4: [(9 * 60 + 30, 11 * 60),   # Friday: 9:30-11:00
        (11 * 60 + 30, 12 * 60 + 30),  # 11:30-12:30
        (13 * 60, 14 * 60),       # 13:00-14:00
        (15 * 60, 15 * 60 + 30),  # 15:00-15:30
        (16 * 60, 16 * 60 + 30)]  # 16:00-16:30
}

# John's busy intervals (in minutes from midnight)
john_busy = {
    0: [(9 * 60, 12 * 60 + 30),   # Monday: 9:00-12:30
        (13 * 60, 14 * 60),       # 13:00-14:00
        (14 * 60 + 30, 16 * 60 + 30)],  # 14:30-16:30
    1: [(9 * 60 + 30, 10 * 60 + 30),  # Tuesday: 9:30-10:30
        (11 * 60 + 30, 13 * 60),       # 11:30-13:00
        (14 * 60, 15 * 60 + 30),       # 14:00-15:30
        (16 * 60 + 30, 17 * 60)],       # 16:30-17:00
    2: [(9 * 60, 12 * 60),        # Wednesday: 9:00-12:00
        (12 * 60 + 30, 13 * 60 + 30),  # 12:30-13:30
        (14 * 60 + 30, 16 * 60)],   # 14:30-16:00
    3: [(9 * 60, 10 * 60 + 30),   # Thursday: 9:00-10:30
        (11 * 60, 11 * 60 + 30),  # 11:00-11:30
        (12 * 60, 13 * 60 + 30),  # 12:00-13:30
        (14 * 60 + 30, 16 * 60)], # 14:30-16:00
    4: [(10 * 60, 10 * 60 + 30),  # Friday: 10:00-10:30
        (12 * 60, 12 * 60 + 30),  # 12:00-12:30
        (13 * 60, 14 * 60),       # 13:00-14:00
        (15 * 60, 15 * 60 + 30),  # 15:00-15:30
        (16 * 60, 17 * 60)]       # 16:00-17:00
}

# Utility function: Given a busy interval [busy_start, busy_end) and a meeting starting at s (of length duration)
# produce a constraint that s does NOT overlap with the busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest meeting time on candidate days
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # s: meeting start time (in minutes after midnight)
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Lawrence's busy constraints on this day
        if day in lawrence_busy:
            for busy_start, busy_end in lawrence_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add John's busy constraints on this day
        if day in john_busy:
            for busy_start, busy_end in john_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Iterate over every possible minute from WORK_START up to latest valid start
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")