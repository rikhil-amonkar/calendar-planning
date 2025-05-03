from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # workday starts at 9:00 (540 minutes)
WORK_END   = 17 * 60   # workday ends at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Danielle's busy intervals (in minutes) per day:
danielle_busy = {
    0: [(9*60 + 30, 10*60), (11*60, 12*60), (13*60, 13*60 + 30)],  # Monday
    1: [(10*60 + 30, 11*60), (15*60 + 30, 16*60)],                  # Tuesday
    2: [(9*60 + 30, 10*60), (12*60 + 30, 13*60)],                    # Wednesday
    4: [(9*60 + 30, 10*60), (12*60, 12*60 + 30), (15*60 + 30, 16*60)] # Friday
}
# Danielle does not want to meet on Thursday, so we exclude day 3

# Amanda's busy intervals (in minutes) per day:
amanda_busy = {
    0: [(9*60 + 30, 10*60 + 30), (11*60, 12*60), (12*60 + 30, 15*60), (15*60 + 30, 17*60)],  # Monday
    1: [(9*60, 10*60 + 30), (11*60, 17*60)],                                              # Tuesday
    2: [(9*60, 9*60 + 30), (10*60 + 30, 12*60 + 30), (13*60, 16*60)],                      # Wednesday
    3: [(9*60, 10*60 + 30), (11*60, 12*60 + 30), (13*60 + 30, 14*60), (16*60, 17*60)],      # Thursday
    4: [(10*60, 10*60 + 30), (12*60, 13*60), (14*60 + 30, 15*60 + 30), (16*60, 17*60)]       # Friday
}

# Allowed days considering Danielle does not want to meet on Thursday:
allowed_days = [0, 1, 2, 4]

# Helper function to ensure the meeting (starting at s, duration minutes long)
# does not overlap with a busy interval (b_start, b_end)
def no_overlap(b_start, b_end, s, duration):
    # Meeting must end before busy interval starts or start after busy ends.
    return Or(s + duration <= b_start, s >= b_end)

def find_earliest_meeting():
    # Iterate over allowed days in order: Monday, Tuesday, Wednesday, Friday.
    for day in allowed_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight for the day

        # Enforce meeting to be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Danielle's busy intervals for the day (if any).
        if day in danielle_busy:
            for (b_start, b_end) in danielle_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Add Amanda's busy intervals for the day (if any).
        if day in amanda_busy:
            for (b_start, b_end) in amanda_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Search for the earliest available start time on this day.
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
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")