from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60   # 9:00 AM = 540 minutes
WORK_END = 17 * 60    # 17:00 = 1020 minutes

# Day encoding
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Amber's busy intervals (in minutes) for each day
amber_busy = {
    0: [ (11 * 60, 11 * 60 + 30) ],                             # Monday: 11:00 to 11:30
    1: [ (9 * 60 + 30, 10 * 60), (14 * 60, 14 * 60 + 30) ],      # Tuesday: 9:30 to 10:00, 14:00 to 14:30
    2: [ (11 * 60, 11 * 60 + 30), (12 * 60, 13 * 60),
         (14 * 60, 15 * 60), (16 * 60 + 30, 17 * 60) ],          # Wednesday: 11:00-11:30, 12:00-13:00, 14:00-15:00, 16:30-17:00
    3: [ (9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60),
         (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60) ],         # Thursday: 9:00-9:30, 10:00-11:00, 13:00-15:00, 15:30-17:00
    4: [ (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 15 * 60),
         (16 * 60, 17 * 60) ]                                  # Friday: 12:30-13:00, 13:30-15:30, 16:00-17:00
}

# Cynthia's busy intervals (in minutes) for each day
cynthia_busy = {
    0: [ (9 * 60, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 17 * 60) ],   # Monday: 9:00-12:30, 13:00-14:30, 15:00-17:00
    1: [ (9 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60),
         (14 * 60 + 30, 17 * 60) ],                                                  # Tuesday: 9:30-12:00, 12:30-13:00, 13:30-14:00, 14:30-17:00
    2: [ (9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60 + 30), (13 * 60 + 30, 17 * 60) ],  # Wednesday: 9:00-9:30, 10:30-12:30, 13:30-17:00
    3: [ (9 * 60 + 30, 12 * 60), (12 * 60 + 30, 16 * 60 + 30) ],                   # Thursday: 9:30-12:00, 12:30-16:30
    4: [ (9 * 60, 9 * 60 + 30), (10 * 60, 12 * 60 + 30), (13 * 60, 15 * 60 + 30),
         (16 * 60, 17 * 60) ]                                                       # Friday: 9:00-9:30, 10:00-12:30, 13:00-15:30, 16:00-17:00
}

# Helper function: a meeting starting at 's' with given duration does not overlap with a busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Ensure the meeting is within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Amber's busy constraints for the day (if any)
        if day in amber_busy:
            for bs, be in amber_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Add Cynthia's busy constraints for the day (if any)
        if day in cynthia_busy:
            for bs, be in cynthia_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Iterate over every possible start time (minute by minute) for the meeting within work hours.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Order the days from Monday to Friday.
ordered_days = [0, 1, 2, 3, 4]
day, start_time = find_earliest_meeting(ordered_days)

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")