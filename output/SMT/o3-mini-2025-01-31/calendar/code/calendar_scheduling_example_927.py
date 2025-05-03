from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration is 1 hour
WORK_START = 9 * 60    # work day starts at 9:00 (540 minutes)
WORK_END = 17 * 60     # work day ends at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Betty's busy intervals (in minutes from midnight)
betty_busy = {
    0: [(9 * 60, 10 * 60)],              # Monday: 9:00-10:00
    1: [(11 * 60 + 30, 12 * 60), (15 * 60, 15 * 60 + 30)],  # Tuesday: 11:30-12:00, 15:00-15:30
    2: [(13 * 60 + 30, 14 * 60)],         # Wednesday: 13:30-14:00
    3: [(16 * 60 + 30, 17 * 60)]          # Thursday: 16:30-17:00
    # Friday: No busy intervals given for Betty.
}

# Roy's busy intervals
roy_busy = {
    0: [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60 + 30), (15 * 60 + 30, 16 * 60 + 30)],  # Monday
    1: [(12 * 60 + 30, 13 * 60), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],                               # Tuesday
    2: [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],  # Wednesday
    3: [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],                                              # Thursday
    4: [(9 * 60, 14 * 60), (15 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)]                       # Friday
}

# Participant preferences:
# Betty would rather not meet on Monday, Wednesday, or Friday.
allowed_days_betty = [1, 3]  # only Tuesday (1) and Thursday (3) are allowed for Betty

# Roy would rather not meet on Tuesday before 13:00.
# We incorporate this as an extra constraint on Tuesday if chosen.

# Helper function to ensure no overlap between meeting and a busy interval.
def no_overlap(b_start, b_end, s, duration):
    # Meeting [s, s+duration] must end before b_start OR start after b_end.
    return Or(s + duration <= b_start, s >= b_end)

def find_earliest_meeting():
    # Iterate over allowed days (Tuesday and Thursday in order)
    for day in allowed_days_betty:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight) for the day

        # Meeting must lie within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # If meeting is on Tuesday, enforce Roy's preference (not before 13:00)
        if day == 1:
            solver.add(s >= 13 * 60)  # 13:00 in minutes

        # Add Betty's busy interval constraints if any exist on that day.
        if day in betty_busy:
            for (b_start, b_end) in betty_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Add Roy's busy interval constraints if any exist on that day.
        if day in roy_busy:
            for (b_start, b_end) in roy_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Check every minute in the working period for a valid starting time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()  # Save current state.
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()  # Backtrack if not satisfiable.
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