from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # in minutes
WORK_START = 9 * 60   # 9:00 -> 540 minutes
WORK_END = 17 * 60    # 17:00 -> 1020 minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Allowed day for Nicole (she cannot meet on Monday, Tuesday, Wednesday, or Friday)
allowed_days_for_nicole = {3}  # Only Thursday is allowed

# Joan's busy intervals in minutes for each day
joan_busy = {
    0: [(10*60+30, 11*60),   # Monday: 10:30-11:00
        (11*60+30, 12*60),   # Monday: 11:30-12:00
        (13*60, 13*60+30)],  # Monday: 13:00-13:30
    1: [(9*60, 9*60+30),     # Tuesday: 9:00-9:30
        (13*60, 13*60+30),   # Tuesday: 13:00-13:30
        (14*60+30, 15*60+30)],# Tuesday: 14:30-15:30
    2: [(10*60+30, 11*60),   # Wednesday: 10:30-11:00
        (12*60, 12*60+30),   # Wednesday: 12:00-12:30
        (14*60, 14*60+30),   # Wednesday: 14:00-14:30
        (15*60+30, 16*60)],  # Wednesday: 15:30-16:00
    3: [(10*60+30, 11*60),   # Thursday: 10:30-11:00
        (12*60, 12*60+30),   # Thursday: 12:00-12:30
        (13*60, 13*60+30),   # Thursday: 13:00-13:30
        (14*60+30, 15*60),   # Thursday: 14:30-15:00
        (16*60+30, 17*60)],  # Thursday: 16:30-17:00
    4: [(9*60+30, 10*60),    # Friday: 9:30-10:00
        (13*60, 14*60),      # Friday: 13:00-14:00
        (16*60, 16*60+30)]    # Friday: 16:00-16:30
}

# Nicole's busy intervals in minutes for each day
nicole_busy = {
    0: [(9*60, 10*60+30),    # Monday: 9:00-10:30
        (11*60, 12*60),      # Monday: 11:00-12:00
        (12*60+30, 13*60),    # Monday: 12:30-13:00
        (13*60+30, 16*60+30)],# Monday: 13:30-16:30
    1: [(9*60, 12*60),       # Tuesday: 9:00-12:00
        (14*60+30, 15*60),    # Tuesday: 14:30-15:00
        (16*60+30, 17*60)],   # Tuesday: 16:30-17:00
    2: [(9*60, 10*60+30),    # Wednesday: 9:00-10:30
        (12*60+30, 13*60+30), # Wednesday: 12:30-13:30
        (15*60, 15*60+30)],   # Wednesday: 15:00-15:30
    3: [(10*60+30, 11*60),    # Thursday: 10:30-11:00
        (14*60+30, 15*60),    # Thursday: 14:30-15:00
        (16*60+30, 17*60)],   # Thursday: 16:30-17:00
    4: [(9*60+30, 10*60),     # Friday: 9:30-10:00
        (10*60+30, 11*60),    # Friday: 10:30-11:00
        (11*60+30, 12*60),    # Friday: 11:30-12:00
        (13*60, 17*60)]       # Friday: 13:00-17:00
}

# A helper function to express that the meeting (starting at s with length duration)
# does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function that finds the earliest meeting time for a given day that satisfies constraints.
def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        # Skip days when Nicole is not available at all.
        if day not in allowed_days_for_nicole:
            continue
        
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        # Meeting must be inside work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Joan's busy constraints for this day, if any.
        if day in joan_busy:
            for busy_start, busy_end in joan_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Nicole's busy constraints for this day, if any.
        if day in nicole_busy:
            for busy_start, busy_end in nicole_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Search for the earliest start time by iterating through each possible minute.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    
    return None, None

# We check days in order: Monday (0), Tuesday (1), Wednesday (2), Thursday (3), Friday (4)
ordered_days = [0, 1, 2, 3, 4]
day, t = find_earliest_meeting(ordered_days)

if day is not None and t is not None:
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")