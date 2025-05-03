from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # duration is 30 minutes
WORK_START = 9 * 60   # 9:00 AM = 540 minutes
WORK_END = 17 * 60    # 17:00 = 1020 minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Sharon's busy intervals (in minutes)
sharon_busy = {
    0: [ (10*60+30, 10*60+30+30),  # Monday: 10:30-11:00
         (13*60+30, 14*60+30),      # Monday: 13:30-14:30
         (16*60, 16*60+30) ],       # Monday: 16:00-16:30
    2: [ (9*60, 9*60+30),          # Wednesday: 9:00-9:30
         (16*60+30, 17*60) ],       # Wednesday: 16:30-17:00
    3: [ (13*60+30, 14*60),        # Thursday: 13:30-14:00
         (15*60, 15*60+30) ],       # Thursday: 15:00-15:30
    4: [ (9*60, 9*60+30),          # Friday: 9:00-9:30
         (13*60+30, 14*60) ]        # Friday: 13:30-14:00
}

# Jose's busy intervals (in minutes)
jose_busy = {
    0: [ (9*60, 17*60) ],         # Monday: 9:00-17:00 (busy all day)
    1: [ (9*60, 10*60+30),         # Tuesday: 9:00-10:30
         (11*60, 17*60) ],         # Tuesday: 11:00-17:00
    2: [ (10*60, 17*60) ],         # Wednesday: 10:00-17:00
    3: [ (9*60, 10*60),           # Thursday: 9:00-10:00
         (10*60+30, 11*60),       # Thursday: 10:30-11:00
         (11*60+30, 13*60),       # Thursday: 11:30-13:00
         (14*60, 16*60),          # Thursday: 14:00-16:00
         (16*60+30, 17*60) ],      # Thursday: 16:30-17:00
    4: [ (9*60, 17*60) ]          # Friday: 9:00-17:00 (busy all day)
}

# Jose does not want to meet on Tuesday, so we will not consider day 1.
# Alternatively, we can add a constraint that prevents scheduling on Tuesday.

# Helper function: meeting starting at s with duration should not overlap with busy interval
def no_overlap(busy_start, busy_end, s, duration):
    # Either the meeting ends before the busy slot, or starts after it.
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest meeting time
def find_earliest_meeting(ordered_days):
    for day in ordered_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes (from midnight)
        
        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Sharon's busy constraints for this day (if any)
        if day in sharon_busy:
            for bs, be in sharon_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Add Jose's busy constraints for this day (if any)
        if day in jose_busy:
            for bs, be in jose_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Iterate over each possible start minute within work hours (earliest first)
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Define the order of days: Monday (0), Tuesday (1), Wednesday (2), Thursday (3), Friday (4)
# But remove Tuesday since Jose does not want to meet on Tuesday.
ordered_days = [0, 2, 3, 4]
day, start_time = find_earliest_meeting(ordered_days)

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")