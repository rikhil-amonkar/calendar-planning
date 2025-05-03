from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 in minutes (540)
WORK_END   = 17 * 60    # 17:00 in minutes (1020)

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Preferences:
# • Virginia would like to avoid more meetings on Wednesday.
# • Kayla would like to avoid more meetings on Monday and Thursday.
# To respect these preferences, we order the candidate days from best to worst:
# Tuesday is best (neither is avoiding Tuesday),
# Wednesday is next (only Virginia prefers to avoid it),
# then Monday (Kayla avoids it),
# and finally Thursday (Kayla avoids it).
candidate_days = [1, 2, 0, 3]

# Busy schedules (times in minutes from midnight)

# Virginia's busy schedule:
# Monday: 10:00-11:30, 12:00-14:30, 15:00-17:00
# Tuesday: 9:00-10:00, 12:00-12:30, 13:00-14:00, 15:00-17:00
# Wednesday: 10:30-11:00, 14:30-15:30
# Thursday: 10:00-10:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 15:30-16:30
virginia_busy = {
    0: [(10*60, 11*60+30), (12*60, 14*60+30), (15*60, 17*60)],
    1: [(9*60, 10*60), (12*60, 12*60+30), (13*60, 14*60), (15*60, 17*60)],
    2: [(10*60+30, 11*60), (14*60+30, 15*60+30)],
    3: [(10*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (15*60+30, 16*60+30)]
}

# Kayla's busy schedule:
# Monday: 9:00-9:30, 12:00-13:00
# Tuesday: 9:00-12:00, 14:00-14:30, 15:00-15:30, 16:30-17:00
# Wednesday: 9:00-10:30, 11:00-16:30
# Thursday: 9:00-10:00, 10:30-11:30, 12:00-17:00
kayla_busy = {
    0: [(9*60, 9*60+30), (12*60, 13*60)],
    1: [(9*60, 12*60), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)],
    2: [(9*60, 10*60+30), (11*60, 16*60+30)],
    3: [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 17*60)]
}

# Utility function: Given a busy interval [busy_start, busy_end) and the meeting start time s,
# the meeting (of the given duration) does not overlap with the busy interval if either:
# - it ends by (or at) busy_start, OR
# - it starts at or after busy_end.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Find an available meeting time on one of the candidate days.
# We search in order of candidate days and for each day we look for the earliest meeting start time.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must start and finish within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Virginia's busy time constraints for this day.
        for busy_start, busy_end in virginia_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Add Kayla's busy time constraints for this day.
        for busy_start, busy_end in kayla_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Search for the earliest valid meeting start time (minute by minute)
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

if selected_day is not None:
    selected_end = selected_start + duration
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")