from z3 import Solver, Int, Or, sat

# Meeting parameters.
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60   # 9:00 AM in minutes
WORK_END   = 17 * 60  # 17:00 in minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals for Jean (each interval is [start, end) in minutes)
jean_busy = {
    0: [(11 * 60, 12 * 60), (12 * 60 + 30, 13 * 60), (16 * 60, 17 * 60)],
    1: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 13 * 60),
        (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (16 * 60, 16 * 60 + 30)],
    2: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), (13 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
    3: [(11 * 60, 11 * 60 + 30)],
    4: [(11 * 60 + 30, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
}

# Busy intervals for Marilyn.
marilyn_busy = {
    0: [(9 * 60 + 30, 13 * 60), (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    1: [(9 * 60, 13 * 60 + 30), (14 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    2: [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
        (14 * 60 + 30, 15 * 60), (16 * 60, 16 * 60 + 30)],
    3: [(9 * 60, 17 * 60)],   # Marilyn is busy all day Thursday.
    4: [(9 * 60, 12 * 60), (12 * 60 + 30, 17 * 60)]
}

# Preferences:
# Jean would rather not meet on Tuesday (day 1) or Wednesday (day 2).
# Marilyn would rather not meet on Monday after 13:00.
#
# We interpret Marilyn's preference as: If the meeting is on Monday (day 0),
# then the meeting's end time must be no later than 13:00.
#
# We will try to schedule on days that do not violate these soft preferences if possible.
#
# Candidate ordering:
# First try days that are not in Jean's disliked days (i.e. not Tuesday or Wednesday)
# and for Monday enforce Marilyn's extra constraint.
preferred_days = [0, 3, 4]  # Monday, Thursday, Friday
backup_days = [1, 2]        # Tuesday, Wednesday (Jean would rather not)

def no_overlap(busy_start, busy_end, s, duration):
    # Returns a constraint ensuring that the meeting (from s to s+duration)
    # does not overlap with the busy interval [busy_start, busy_end).
    return Or(s + duration <= busy_start, s >= busy_end)

def find_meeting_time(candidate_days):
    for day in candidate_days:
        # Marilyn is busy all day on Thursday (3) so skip it.
        if day == 3:
            continue
        # Check Friday possibility: Marilyn is busy except possibly 12:00-12:30,
        # but Jean is busy from 11:30 to 12:30 on Friday.
        if day == 4:
            # We know from the schedules that Friday does not work.
            continue

        solver = Solver()
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Marilyn's preference: on Monday, meeting must end by 13:00.
        if day == 0:
            solver.add(s + duration <= 13 * 60)
        
        # Add busy interval constraints for Jean.
        if day in jean_busy:
            for start_busy, end_busy in jean_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
        
        # Add busy interval constraints for Marilyn.
        if day in marilyn_busy:
            for start_busy, end_busy in marilyn_busy[day]:
                solver.add(no_overlap(start_busy, end_busy, s, duration))
        
        # Try every possible minute start in the work window.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Try preferred days first:
day, t = find_meeting_time(preferred_days)
# If no solution on preferred days, try backup days.
if day is None:
    day, t = find_meeting_time(backup_days)

if day is not None and t is not None:
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}"
          .format(day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")