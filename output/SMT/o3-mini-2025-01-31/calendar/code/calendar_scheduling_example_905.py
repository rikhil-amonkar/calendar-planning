from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes
WORK_START = 9 * 60     # 9:00 AM in minutes (540)
WORK_END   = 17 * 60    # 17:00 (1020)

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals for Amy (times in minutes)
amy_busy = {
    0: [(10 * 60 + 30, 11 * 60),   # Monday: 10:30-11:00
        (13 * 60, 13 * 60 + 30)],   # Monday: 13:00-13:30
    1: [(9 * 60 + 30, 10 * 60 + 30),  # Tuesday: 9:30-10:30
        (13 * 60 + 30, 14 * 60 + 30)], # Tuesday: 13:30-14:30
    2: [(9 * 60 + 30, 10 * 60 + 30),  # Wednesday: 9:30-10:30
        (11 * 60 + 30, 12 * 60),       # Wednesday: 11:30-12:00
        (13 * 60 + 30, 14 * 60 + 30),   # Wednesday: 13:30-14:30
        (15 * 60 + 30, 17 * 60)],       # Wednesday: 15:30-17:00
    3: [(9 * 60, 9 * 60 + 30),         # Thursday: 9:00-9:30
        (14 * 60 + 30, 15 * 60),       # Thursday: 14:30-15:00
        (15 * 60 + 30, 16 * 60)],      # Thursday: 15:30-16:00
    4: [(12 * 60 + 30, 13 * 60 + 30),   # Friday: 12:30-13:30
        (15 * 60 + 30, 16 * 60)]       # Friday: 15:30-16:00
}

# Busy intervals for Anna (times in minutes)
anna_busy = {
    0: [(9 * 60, 13 * 60),           # Monday: 9:00-13:00
        (13 * 60 + 30, 17 * 60)],     # Monday: 13:30-17:00
    1: [(9 * 60, 11 * 60),           # Tuesday: 9:00-11:00
        (11 * 60 + 30, 17 * 60)],     # Tuesday: 11:30-17:00
    2: [(9 * 60 + 30, 10 * 60),      # Wednesday: 9:30-10:00
        (10 * 60 + 30, 11 * 60 + 30),  # Wednesday: 10:30-11:30
        (12 * 60, 14 * 60),           # Wednesday: 12:00-14:00
        (15 * 60, 15 * 60 + 30),      # Wednesday: 15:00-15:30
        (16 * 60, 16 * 60 + 30)],     # Wednesday: 16:00-16:30
    3: [(9 * 60 + 30, 17 * 60)],      # Thursday: 9:30-17:00
    4: [(9 * 60, 10 * 60),           # Friday: 9:00-10:00
        (10 * 60 + 30, 13 * 60),      # Friday: 10:30-13:00
        (13 * 60 + 30, 14 * 60),      # Friday: 13:30-14:00
        (14 * 60 + 30, 15 * 60),      # Friday: 14:30-15:00
        (15 * 60 + 30, 17 * 60)]      # Friday: 15:30-17:00
}

# Preferences:
# Amy would like to avoid additional meetings on Wednesday (day 2).
# Anna does not want to meet on Friday (day 4).

# We'll consider candidate days that respect the hard preferences (Anna)
# and try to avoid Wednesday if possible.
# Thus we eliminate Friday for Anna, i.e., candidate days: Monday, Tuesday, Thursday.
# And prefer Monday, Tuesday, Thursday over Wednesday (used only if no other option).
candidate_days = [0, 1, 3, 2]  # try Monday, Tuesday, Thursday first; then Wednesday if needed

def no_overlap(busy_start, busy_end, s, duration):
    # Returns a constraint to ensure the meeting starting at s (lasting duration)
    # does not overlap with a busy interval [busy_start, busy_end).
    return Or(s + duration <= busy_start, s >= busy_end)

def find_meeting_time(days):
    for day in days:
        # Hard preference: Anna does not want to meet on Friday (day 4)
        if day == 4:
            continue
        # Soft preference for Amy: try to avoid Wednesday (day 2)
        # We'll check Wednesday only if no other day works.
        if day == 2 and any(d != 2 for d in days if d != 4):
            # Skip Wednesday in the first pass to honor Amy's wish.
            continue

        solver = Solver()
        # Integer variable for meeting start time (in minutes since midnight)
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add busy constraints for Amy
        if day in amy_busy:
            for busy_start, busy_end in amy_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        # Add busy constraints for Anna
        if day in anna_busy:
            for busy_start, busy_end in anna_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Attempt to find a meeting start time by trying all minutes within the work window.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()

    # If no meeting could be found respecting soft preference for Amy,
    # allow Wednesday even though Amy prefers not to.
    if 2 not in days:
        days.append(2)
    for day in days:
        if day != 2:
            continue  # only check Wednesday now
        solver = Solver()
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        if day in amy_busy:
            for busy_start, busy_end in amy_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        if day in anna_busy:
            for busy_start, busy_end in anna_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Run the search for a meeting time.
day, t = find_meeting_time(candidate_days)

if day is not None and t is not None:
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("A valid meeting is scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")