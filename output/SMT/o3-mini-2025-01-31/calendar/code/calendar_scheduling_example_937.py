from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60   # 9:00 in minutes from midnight (540)
WORK_END = 17 * 60    # 17:00 in minutes from midnight (1020)

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals for Jesse (times in minutes from midnight)
# Monday: 9:30-10:00, 10:30-11:00, 13:00-15:30, 16:00-17:00
# Tuesday: 10:00-11:00, 12:00-13:00, 14:30-15:00, 15:30-16:00
# Wednesday: 11:30-12:00, 14:00-15:00
# Thursday: 9:00-9:30, 10:00-10:30, 11:30-12:00, 13:00-15:30, 16:00-16:30
# Friday: 9:30-10:00, 10:30-11:30, 12:00-12:30, 13:30-14:00, 15:30-16:30
jesse_busy = {
    0: [(9*60+30, 10*60), (10*60+30, 11*60), (13*60, 15*60+30), (16*60, 17*60)],
    1: [(10*60, 11*60), (12*60, 13*60), (14*60+30, 15*60), (15*60+30, 16*60)],
    2: [(11*60+30, 12*60), (14*60, 15*60)],
    3: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60+30, 12*60), (13*60, 15*60+30), (16*60, 16*60+30)],
    4: [(9*60+30, 10*60), (10*60+30, 11*60+30), (12*60, 12*60+30), (13*60+30, 14*60), (15*60+30, 16*60+30)]
}

# Busy intervals for Lori (times in minutes from midnight)
# Monday: 9:00-10:30, 11:00-13:00, 13:30-14:00, 15:00-15:30, 16:00-17:00
# Tuesday: 9:00-9:30, 10:30-11:30, 12:00-12:30, 14:00-16:00
# Wednesday: 9:00-10:00, 12:00-12:30, 13:00-14:00, 14:30-15:00
# Thursday: 9:30-11:00, 11:30-12:30, 13:30-14:00, 14:30-15:00, 16:00-16:30
# Friday: 9:30-10:00, 11:00-12:30, 13:00-15:00, 16:00-16:30
lori_busy = {
    0: [(9*60, 10*60+30), (11*60, 13*60), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 17*60)],
    1: [(9*60, 9*60+30), (10*60+30, 11*60+30), (12*60, 12*60+30), (14*60, 16*60)],
    2: [(9*60, 10*60), (12*60, 12*60+30), (13*60, 14*60), (14*60+30, 15*60)],
    3: [(9*60+30, 11*60), (11*60+30, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60), (16*60, 16*60+30)],
    4: [(9*60+30, 10*60), (11*60, 12*60+30), (13*60, 15*60), (16*60, 16*60+30)]
}

# Additional constraints: 
# Jesse cannot meet on Tuesday (day 1) or Friday (day 4)
# Lori cannot meet on Monday (day 0)

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # Ensure meeting ends before a busy interval or starts after it ends.
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # We'll iterate over the days Monday (0) to Friday (4)
    for day in range(5):
        # Skip days that are not allowed by either participant.
        if day in [1, 4]:  # Jesse cannot meet on Tuesday (1) or Friday (4)
            continue
        if day == 0:      # Lori cannot meet on Monday (0)
            continue

        solver = Solver()
        # s: meeting start time (in minutes from midnight) on the chosen day.
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Jesse's busy intervals for the day
        if day in jesse_busy:
            for (busy_start, busy_end) in jesse_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Lori's busy intervals for the day
        if day in lori_busy:
            for (busy_start, busy_end) in lori_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Try every minute in the work day for a valid meeting start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hour, start_min = divmod(start_time, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time found that satisfies all constraints.")