from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END   = 17 * 60    # 17:00 → 1020 minutes

# Days encoding:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# Existing calendar information:
# • Sandra is busy all day on Monday.
# • Tuesday does not offer any common free slot.
# Preferences:
# • Adam would like to avoid meetings on Wednesday after 12:30.
# • Adam would rather avoid Thursday.
# Thus, we first try Wednesday with the extra time constraint,
# and if that fails (it shouldn’t), we would consider Thursday.
candidate_days = [2, 3]

# Adam's busy intervals (in minutes after midnight):
# Monday: 9:00-9:30, 10:30-11:00, 12:00-12:30, 13:00-14:00, 14:30-15:00
# Tuesday: 12:30-15:00, 16:00-17:00
# Wednesday: 9:00-10:30, 12:00-14:00, 14:30-15:30, 16:00-17:00
# Thursday: 9:00-9:30, 12:00-13:30
adam_busy = {
    0: [(9*60, 9*60+30), (10*60+30, 11*60), (12*60, 12*60+30),
        (13*60, 14*60), (14*60+30, 15*60)],
    1: [(12*60+30, 15*60), (16*60, 17*60)],
    2: [(9*60, 10*60+30), (12*60, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
    3: [(9*60, 9*60+30), (12*60, 13*60+30)]
}

# Sandra's busy intervals:
# Monday: 9:00-17:00
# Tuesday: 9:00-14:00, 14:30-16:30
# Wednesday: 9:00-10:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 15:00-17:00
# Thursday: 9:00-11:30, 12:30-17:00
sandra_busy = {
    0: [(9*60, 17*60)],
    1: [(9*60, 14*60), (14*60+30, 16*60+30)],
    2: [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30),
        (13*60, 13*60+30), (15*60, 17*60)],
    3: [(9*60, 11*60+30), (12*60+30, 17*60)]
}

# Utility function that ensures the meeting starting at 's'
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Find a meeting time that satisfies all constraints over the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes after midnight

        # Meeting must lie completely within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add additional constraint for Wednesday:
        # Adam prefers no meetings after 12:30 on Wednesday.
        if day == 2:
            # Meeting must finish by 12:30 → s + duration <= 750.
            solver.add(s + duration <= 12*60 + 30)

        # Add Adam's busy constraints for the day.
        for busy_start, busy_end in adam_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Add Sandra's busy constraints for the day.
        for busy_start, busy_end in sandra_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Try each possible starting minute and return the earliest solution.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()

    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    selected_day = day_names[day]
    selected_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(selected_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(selected_day, start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")