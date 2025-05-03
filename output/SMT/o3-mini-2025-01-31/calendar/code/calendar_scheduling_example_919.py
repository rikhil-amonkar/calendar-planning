from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60   # 9:00 AM = 540 minutes
WORK_END = 17 * 60    # 17:00 = 1020 minutes

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Joshua's busy intervals (in minutes)
joshua_busy = {
    0: [(12 * 60 + 30, 13 * 60)],    # Monday: 12:30 to 13:00
    1: [(13 * 60, 13 * 60 + 30)]      # Tuesday: 13:00 to 13:30
    # No busy intervals mentioned for Wednesday, Thursday, Friday.
}

# Vincent's busy intervals (in minutes)
vincent_busy = {
    0: [ (9 * 60, 10 * 60 + 30),      # Monday: 9:00 to 10:30
         (11 * 60, 12 * 60),          # Monday: 11:00 to 12:00
         (13 * 60 + 30, 14 * 60 + 30),# Monday: 13:30 to 14:30
         (15 * 60 + 30, 16 * 60) ],   # Monday: 15:30 to 16:00
    1: [ (9 * 60, 11 * 60),           # Tuesday: 9:00 to 11:00
         (11 * 60 + 30, 12 * 60),     # Tuesday: 11:30 to 12:00
         (14 * 60, 15 * 60) ],        # Tuesday: 14:00 to 15:00
    2: [ (9 * 60 + 30, 10 * 60),      # Wednesday: 9:30 to 10:00
         (11 * 60, 11 * 60 + 30),     # Wednesday: 11:00 to 11:30
         (12 * 60, 13 * 60),          # Wednesday: 12:00 to 13:00
         (14 * 60, 15 * 60),          # Wednesday: 14:00 to 15:00
         (15 * 60 + 30, 16 * 60) ],   # Wednesday: 15:30 to 16:00
    3: [ (9 * 60, 10 * 60 + 30),      # Thursday: 9:00 to 10:30
         (11 * 60 + 30, 14 * 60 + 30),# Thursday: 11:30 to 14:30
         (16 * 60 + 30, 17 * 60) ],   # Thursday: 16:30 to 17:00
    4: [ (9 * 60, 11 * 60),           # Friday: 9:00 to 11:00
         (12 * 60, 12 * 60 + 30),     # Friday: 12:00 to 12:30
         (13 * 60 + 30, 14 * 60),     # Friday: 13:30 to 14:00
         (14 * 60 + 30, 16 * 60 + 30) ]  # Friday: 14:30 to 16:30
}

# Joshua cannot meet on Thursday, so allowed days are:
allowed_days = [0, 1, 2, 4]  # Monday, Tuesday, Wednesday, Friday

# Helper function: ensures that a meeting starting at 's' with given duration does not conflict with a busy period.
def no_overlap(busy_start, busy_end, s, duration):
    # The meeting ends before the busy period starts, or it starts after the busy period ends.
    return Or(s + duration <= busy_start, s >= busy_end)

def find_earliest_meeting(days):
    # Iterate through the allowed days in order
    for day in days:
        solver = Solver()
        s = Int("s")  # start time variable in minutes from midnight
        
        # Enforce the meeting to happen within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Joshua's busy constraints for the day, if any
        if day in joshua_busy:
            for bs, be in joshua_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
        
        # Add Vincent's busy constraints for the day, if any
        if day in vincent_busy:
            for bs, be in vincent_busy[day]:
                solver.add(no_overlap(bs, be, s, duration))
                
        # Iterate minute-by-minute to find the earliest possible start time
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