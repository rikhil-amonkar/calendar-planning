from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # work hours start at 9:00 (540 minutes)
WORK_END   = 17 * 60   # work hours end at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Debra's busy intervals per day (times in minutes from midnight)
debra_busy = {
    0: [(10*60, 11*60), (11*60 + 30, 14*60)],                  # Monday
    1: [(11*60, 11*60 + 30), (14*60, 14*60 + 30)],              # Tuesday
    2: [(10*60, 10*60 + 30), (12*60, 13*60), (13*60 + 30, 14*60), (15*60, 15*60 + 30), (16*60 + 30, 17*60)],  # Wednesday
    3: [(9*60 + 30, 10*60), (12*60 + 30, 14*60), (16*60, 17*60)],# Thursday
    4: [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (14*60, 14*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]  # Friday
}

# Eugene's busy intervals per day
eugene_busy = {
    0: [(9*60, 9*60 + 30), (10*60, 11*60 + 30), (12*60, 14*60), (14*60 + 30, 15*60 + 30), (16*60, 17*60)],  # Monday
    1: [(9*60, 10*60), (10*60 + 30, 11*60), (12*60, 12*60 + 30), (13*60, 14*60), (16*60, 16*60 + 30)],   # Tuesday
    2: [(9*60, 10*60), (11*60, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)],   # Wednesday
    3: [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 15*60 + 30), (16*60, 16*60 + 30)],  # Thursday
    4: [(9*60 + 30, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 17*60)]   # Friday
}

# Eugene would rather not meet on Monday, Wednesday, Thursday, or Friday.
# So the only allowed day for the meeting is Tuesday.
allowed_days = [1]  # Tuesday only

# Helper function to ensure that a meeting starting at time 's' (for 'duration' minutes)
# does not overlap with a busy interval (b_start, b_end)
def no_overlap(b_start, b_end, s, duration):
    # The meeting either finishes before the busy interval starts or starts after the busy interval ends.
    return Or(s + duration <= b_start, s >= b_end)

def find_earliest_meeting():
    # Only check allowed days (in our case, just Tuesday)
    for day in allowed_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight for the chosen day

        # The meeting must lie within work hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add constraints for Debra's busy intervals (if any) for the day
        if day in debra_busy:
            for (b_start, b_end) in debra_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Add constraints for Eugene's busy intervals (if any) for the day
        if day in eugene_busy:
            for (b_start, b_end) in eugene_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Iterate through possible start times from WORK_START to last possible minute
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