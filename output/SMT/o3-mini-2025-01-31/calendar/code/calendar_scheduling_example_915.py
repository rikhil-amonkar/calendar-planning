from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60   # 9:00 AM in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Christine's busy intervals (in minutes) for each day
christine_busy = {
    0: [ (10*60, 10*60+30),     # Monday: 10:00 - 10:30
         (14*60, 14*60+30),     # Monday: 14:00 - 14:30
         (15*60, 15*60+30) ],   # Monday: 15:00 - 15:30
    1: [ (10*60, 10*60+30) ],   # Tuesday: 10:00 - 10:30
    2: [ (9*60, 10*60),        # Wednesday: 9:00 - 10:00
         (13*60, 13*60+30),     # Wednesday: 13:00 - 13:30
         (14*60, 14*60+30) ],   # Wednesday: 14:00 - 14:30
    3: [ (9*60, 11*60),        # Thursday: 9:00 - 11:00
         (11*60+30, 12*60+30),  # Thursday: 11:30 - 12:30
         (13*60+30, 14*60+30),  # Thursday: 13:30 - 14:30
         (15*60, 16*60),        # Thursday: 15:00 - 16:00
         (16*60+30, 17*60) ],   # Thursday: 16:30 - 17:00
    4: [ (9*60, 9*60+30),       # Friday: 9:00 - 9:30
         (10*60, 10*60+30),     # Friday: 10:00 - 10:30
         (11*60, 12*60+30),     # Friday: 11:00 - 12:30
         (13*60+30, 14*60),     # Friday: 13:30 - 14:00
         (15*60+30, 16*60) ]    # Friday: 15:30 - 16:00
}

# Keith's busy intervals (in minutes) for each day
keith_busy = {
    0: [ (9*60, 17*60) ],       # Monday: 9:00 - 17:00 (busy all day)
    1: [ (9*60, 17*60) ],       # Tuesday: 9:00 - 17:00 (busy all day)
    2: [ (9*60, 10*60+30),      # Wednesday: 9:00 - 10:30
         (11*60, 15*60),        # Wednesday: 11:00 - 15:00
         (15*60+30, 17*60) ],    # Wednesday: 15:30 - 17:00
    3: [ (9*60, 9*60+30),       # Thursday: 9:00 - 9:30
         (10*60, 15*60),        # Thursday: 10:00 - 15:00
         (15*60+30, 17*60) ],    # Thursday: 15:30 - 17:00
    4: [ (9*60+30, 12*60),      # Friday: 9:30 - 12:00
         (13*60+30, 17*60) ]     # Friday: 13:30 - 17:00
}

# Helper function to ensure that the meeting starting at 's' for 'duration' does not overlap with a busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    # Either meeting ends before the busy interval, or starts after the busy interval.
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest meeting time by iterating over days and possible start times.
def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must be within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Christine's busy constraints for the day.
        if day in christine_busy:
            for busy_start, busy_end in christine_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Keith's busy constraints for the day.
        if day in keith_busy:
            for busy_start, busy_end in keith_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Iterate over every possible starting minute within work hours.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Order days from Monday to Friday
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