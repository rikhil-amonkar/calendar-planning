from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 AM = 540 minutes
WORK_END = 17 * 60    # 17:00 = 1020 minutes

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Cheryl's busy intervals (in minutes)
cheryl_busy = {
    0: [ (13 * 60 + 30, 14 * 60) ],           # Monday: 13:30-14:00
    2: [ (10 * 60, 10 * 60 + 30),               # Wednesday: 10:00-10:30
         (14 * 60 + 30, 15 * 60) ],             # Wednesday: 14:30-15:00
    3: [ (10 * 60, 10 * 60 + 30) ],             # Thursday: 10:00-10:30
    4: [ (11 * 60, 12 * 60) ]                   # Friday: 11:00-12:00
}

# Brittany's busy intervals (in minutes)
brittany_busy = {
    0: [ (9 * 60, 10 * 60),                     # Monday: 9:00-10:00
         (11 * 60, 12 * 60),                    # Monday: 11:00-12:00
         (12 * 60 + 30, 13 * 60),               # Monday: 12:30-13:00
         (14 * 60, 15 * 60),                    # Monday: 14:00-15:00
         (15 * 60 + 30, 16 * 60),               # Monday: 15:30-16:00
         (16 * 60 + 30, 17 * 60) ],             # Monday: 16:30-17:00
    1: [ (9 * 60 + 30, 10 * 60),                # Tuesday: 9:30-10:00
         (10 * 60 + 30, 17 * 60) ],             # Tuesday: 10:30-17:00
    2: [ (10 * 60, 10 * 60 + 30),               # Wednesday: 10:00-10:30
         (12 * 60, 13 * 60),                    # Wednesday: 12:00-13:00
         (13 * 60 + 30, 14 * 60 + 30),           # Wednesday: 13:30-14:30
         (16 * 60 + 30, 17 * 60) ],             # Wednesday: 16:30-17:00
    3: [ (10 * 60, 10 * 60 + 30),               # Thursday: 10:00-10:30
         (13 * 60, 13 * 60 + 30),               # Thursday: 13:00-13:30
         (16 * 60 + 30, 17 * 60) ],             # Thursday: 16:30-17:00
    4: [ (9 * 60, 10 * 60),                     # Friday: 9:00-10:00
         (11 * 60, 11 * 60 + 30),               # Friday: 11:00-11:30
         (12 * 60 + 30, 13 * 60),               # Friday: 12:30-13:00
         (13 * 60 + 30, 15 * 60),               # Friday: 13:30-15:00
         (15 * 60 + 30, 16 * 60) ]              # Friday: 15:30-16:00
}

# Participants' day preferences:
# Cheryl would rather not meet on Wednesday (day 2)
# Brittany does not want to meet on Monday (day 0)
# Therefore, we remove day 0 and day 2 from our list of candidate days.
allowed_days = [1, 3, 4]  # Tuesday, Thursday, Friday

# Helper function: given a busy interval (bs, be), ensure that a meeting starting at time `s`
# with given duration does not overlap with the busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Enforce meeting to be within the work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Cheryl's busy constraints for the day (if any)
        if day in cheryl_busy:
            for bs, be in cheryl_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Add Brittany's busy constraints for the day (if any)
        if day in brittany_busy:
            for bs, be in brittany_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
                
        # Iterate minute by minute for possible start times, to find the earliest available time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Respecting preferences, we check allowed days in order: Tuesday (1), Thursday (3), then Friday (4)
day, start_time = find_earliest_meeting(allowed_days)

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")