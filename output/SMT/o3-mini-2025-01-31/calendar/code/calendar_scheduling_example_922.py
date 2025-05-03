from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60   # workday starts at 9:00 (540 minutes)
WORK_END   = 17 * 60  # workday ends at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Bobby's busy intervals (in minutes)
bobby_busy = {
    0: [ (9*60 + 30, 10*60 + 30),    # Monday: 9:30 to 10:30
         (11*60 + 30, 12*60),         # Monday: 11:30 to 12:00
         (14*60 + 30, 15*60 + 30),     # Monday: 14:30 to 15:30
         (16*60, 16*60 + 30) ],        # Monday: 16:00 to 16:30
    1: [ (9*60, 10*60),             # Tuesday: 9:00 to 10:00
         (10*60 + 30, 11*60 + 30),    # Tuesday: 10:30 to 11:30
         (14*60, 15*60),             # Tuesday: 14:00 to 15:00
         (15*60 + 30, 16*60),         # Tuesday: 15:30 to 16:00
         (16*60 + 30, 17*60) ],       # Tuesday: 16:30 to 17:00
    2: [ (9*60 + 30, 10*60),         # Wednesday: 9:30 to 10:00
         (10*60 + 30, 11*60 + 30),    # Wednesday: 10:30 to 11:30
         (12*60, 13*60),             # Wednesday: 12:00 to 13:00
         (14*60 + 30, 15*60),         # Wednesday: 14:30 to 15:00
         (15*60 + 30, 17*60) ],       # Wednesday: 15:30 to 17:00
    4: [ (9*60, 11*60),             # Friday: 9:00 to 11:00
         (12*60, 13*60),            # Friday: 12:00 to 13:00
         (13*60 + 30, 14*60 + 30),    # Friday: 13:30 to 14:30
         (16*60, 16*60 + 30) ]        # Friday: 16:00 to 16:30
}
# (Bobby has no meetings provided for Thursday; his calendar is free that day.)

# Brandon's busy intervals (in minutes)
brandon_busy = {
    0: [ (10*60, 11*60),         # Monday: 10:00 to 11:00
         (11*60 + 30, 13*60),     # Monday: 11:30 to 13:00
         (13*60 + 30, 14*60),     # Monday: 13:30 to 14:00
         (14*60 + 30, 17*60) ],   # Monday: 14:30 to 17:00
    1: [ (10*60, 10*60 + 30),     # Tuesday: 10:00 to 10:30
         (11*60 + 30, 12*60),     # Tuesday: 11:30 to 12:00
         (12*60 + 30, 13*60 + 30), # Tuesday: 12:30 to 13:30
         (15*60 + 30, 16*60 + 30) ],# Tuesday: 15:30 to 16:30
    2: [ (9*60, 10*60),          # Wednesday: 9:00 to 10:00
         (10*60 + 30, 11*60),     # Wednesday: 10:30 to 11:00
         (11*60 + 30, 12*60 + 30), # Wednesday: 11:30 to 12:30
         (13*60, 13*60 + 30),     # Wednesday: 13:00 to 13:30
         (14*60 + 30, 15*60 + 30), # Wednesday: 14:30 to 15:30
         (16*60 + 30, 17*60) ],   # Wednesday: 16:30 to 17:00
    3: [ (9*60, 11*60),          # Thursday: 9:00 to 11:00
         (11*60 + 30, 12*60),     # Thursday: 11:30 to 12:00
         (13*60, 14*60 + 30),     # Thursday: 13:00 to 14:30
         (15*60, 16*60) ],        # Thursday: 15:00 to 16:00
    4: [ (9*60 + 30, 10*60 + 30), # Friday: 9:30 to 10:30
         (11*60, 11*60 + 30),     # Friday: 11:00 to 11:30
         (12*60, 13*60),         # Friday: 12:00 to 13:00
         (13*60 + 30, 14*60 + 30), # Friday: 13:30 to 14:30
         (15*60 + 30, 16*60) ]     # Friday: 15:30 to 16:00
}

# Preferences:
# Bobby would like to avoid more meetings on Thursday and Friday,
# so his preferred days are Monday, Tuesday, or Wednesday.
# Brandon would like to avoid meetings on Monday and Tuesday,
# and if on Wednesday, he would prefer the meeting start at or after 12:00.
# Thus, the only day that satisfies both preferences is Wednesday (day 2).

allowed_days = [2]

# Helper function: the meeting (from s to s+duration) must NOT overlap a busy interval.
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Enforce meeting to be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Enforce Brandon's preference on Wednesday: avoid meetings before 12:00.
        if day == 2:
            solver.add(s >= 12 * 60)

        # Add Bobby's busy intervals if any on this day.
        if day in bobby_busy:
            for bs, be in bobby_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))

        # Add Brandon's busy intervals if any on this day.
        if day in brandon_busy:
            for bs, be in brandon_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))

        # Try every minute in the work hours for this day to get the earliest option.
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