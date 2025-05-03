from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # 9:00 AM in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# James' busy intervals (in minutes)
james_busy = {
    0: [ (11 * 60 + 30, 12 * 60),  # Monday: 11:30 to 12:00
         (13 * 60 + 30, 14 * 60),  # Monday: 13:30 to 14:00
         (15 * 60 + 30, 16 * 60) ],# Monday: 15:30 to 16:00
    1: [ (10 * 60 + 30, 11 * 60) ],# Tuesday: 10:30 to 11:00
    3: [ (15 * 60, 15 * 60 + 30) ],# Thursday: 15:00 to 15:30
    4: [ (12 * 60 + 30, 13 * 60) ] # Friday: 12:30 to 13:00
}

# Jacob's busy intervals (in minutes)
jacob_busy = {
    0: [ (9 * 60, 10 * 60),        # Monday: 9:00 to 10:00
         (10 * 60 + 30, 11 * 60 + 30),  # Monday: 10:30 to 11:30
         (12 * 60, 13 * 60 + 30),   # Monday: 12:00 to 13:30
         (14 * 60, 15 * 60),        # Monday: 14:00 to 15:00
         (16 * 60, 16 * 60 + 30) ], # Monday: 16:00 to 16:30
    1: [ (9 * 60 + 30, 10 * 60 + 30),  # Tuesday: 9:30 to 10:30
         (11 * 60, 11 * 60 + 30),   # Tuesday: 11:00 to 11:30
         (12 * 60, 12 * 60 + 30),   # Tuesday: 12:00 to 12:30
         (13 * 60 + 30, 14 * 60 + 30),# Tuesday: 13:30 to 14:30
         (15 * 60, 16 * 60),        # Tuesday: 15:00 to 16:00
         (16 * 60 + 30, 17 * 60) ], # Tuesday: 16:30 to 17:00
    2: [ (9 * 60, 17 * 60) ],      # Wednesday: busy all day
    3: [ (10 * 60, 10 * 60 + 30),  # Thursday: 10:00 to 10:30
         (13 * 60, 13 * 60 + 30),  # Thursday: 13:00 to 13:30
         (14 * 60 + 30, 15 * 60),  # Thursday: 14:30 to 15:00
         (16 * 60, 16 * 60 + 30) ],# Thursday: 16:00 to 16:30
    4: [ (9 * 60, 9 * 60 + 30),    # Friday: 9:00 to 9:30
         (10 * 60, 10 * 60 + 30),  # Friday: 10:00 to 10:30
         (11 * 60, 12 * 60),       # Friday: 11:00 to 12:00
         (13 * 60 + 30, 15 * 60 + 30),# Friday: 13:30 to 15:30
         (16 * 60 + 30, 17 * 60) ]  # Friday: 16:30 to 17:00
}

# Preferences:
# - James would like to avoid more meetings on Monday after 14:00:
#     If the meeting is on Monday, then the meeting must end by 14:00.
# - Jacob would like to avoid meetings on Tuesday, Thursday and Friday.
#   (Given these preferences and his full-day busy schedule on Wednesday, the only day left is Monday.)
#
# Thus, we restrict the allowed days to Monday (day 0).
allowed_days = [0]

# Helper function to enforce that the meeting does not overlap with a busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    # Meeting (from s to s+duration) must either finish before busy_start or start after busy_end.
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Enforce the meeting within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # If the meeting is on Monday, add James' preference to avoid after 14:00.
        if day == 0:
            solver.add(s + duration <= 14 * 60)  # meeting must end by 14:00
        
        # Add James' busy intervals for the day.
        if day in james_busy:
            for bs, be in james_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
                
        # Add Jacob's busy intervals for the day.
        if day in jacob_busy:
            for bs, be in jacob_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Search for the earliest time slot minute-by-minute in the available window.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, start_time = find_earliest_meeting(allowed_days)

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")