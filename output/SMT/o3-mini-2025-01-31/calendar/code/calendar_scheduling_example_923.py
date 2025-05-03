from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60   # 9:00 in minutes
WORK_END   = 17 * 60  # 17:00 in minutes

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Kyle's busy intervals (in minutes) per day:
# For each interval, (start, end)
kyle_busy = {
    0: [(10*60 + 30, 11*60)],  # Monday: 10:30 to 11:00
    1: [(10*60, 11*60), (12*60, 12*60 + 30), (13*60 + 30, 14*60)],  # Tuesday
    2: [(10*60, 10*60 + 30), (12*60, 12*60 + 30), (13*60 + 30, 14*60)],  # Wednesday
    3: [(14*60 + 30, 15*60)],  # Thursday: 14:30 to 15:00
    4: [(10*60, 10*60 + 30), (13*60, 13*60 + 30), (16*60 + 30, 17*60)]   # Friday
}

# Sharon's busy intervals (in minutes) per day:
sharon_busy = {
    0: [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 14*60 + 30), (15*60, 15*60 + 30)],
    1: [(9*60, 10*60), (10*60 + 30, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 15*60), (16*60 + 30, 17*60)],
    2: [(9*60, 11*60 + 30), (12*60, 14*60 + 30), (15*60, 17*60)],
    3: [(9*60 + 30, 15*60 + 30), (16*60, 17*60)],
    4: [(9*60, 10*60), (10*60 + 30, 11*60 + 30), (12*60 + 30, 13*60), (13*60 + 30, 14*60 + 30), (15*60, 17*60)]
}

# The group would like to meet at their earliest availability.
# We search in day order: Monday (0) through Friday (4).

# Helper function: meeting starting at 's' minutes with length 'duration' should not overlap a busy interval (b_start, b_end)
def no_overlap(b_start, b_end, s, duration):
    # Either the meeting finishes prior to the busy interval, or starts after it.
    return Or(s + duration <= b_start, s >= b_end)

def find_earliest_meeting():
    # Iterate the days in order Monday to Friday
    for day in range(5):
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes) for the chosen day
        
        # The meeting must be within work hours:
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add constraints for Kyle's busy intervals on this day (if any)
        if day in kyle_busy:
            for (b_start, b_end) in kyle_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))
        
        # Add constraints for Sharon's busy intervals on this day (if any)
        if day in sharon_busy:
            for (b_start, b_end) in sharon_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))
        
        # Now, search for the earliest available minute on this day.
        # We iterate from the beginning of work day to the last possible start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                # Found a valid meeting start time on this day.
                return day, t
            solver.pop()
    return None, None

day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")