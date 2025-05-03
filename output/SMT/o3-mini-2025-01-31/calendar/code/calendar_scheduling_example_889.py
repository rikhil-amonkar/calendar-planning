from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END   = 17 * 60    # 17:00 → 1020 minutes

# Days encoding:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# Based on the preferences:
# - Danielle does not want to meet on Wednesday.
# - Angela would rather not meet on Tuesday or Thursday.
# Thus, the only candidate day is Monday.
candidate_days = [0]

# Danielle's busy intervals (in minutes since midnight):
# Monday: 9:00-9:30, 13:30-14:00, 14:30-15:30, 16:00-16:30
# Tuesday: 10:30-11:00, 12:00-12:30
# Wednesday: 11:30-12:00, 13:30-14:00, 15:00-15:30
# Thursday: 9:00-10:00, 11:30-12:00, 16:30-17:00
danielle_busy = {
    0: [(9*60, 9*60+30), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 16*60+30)],
    1: [(10*60+30, 11*60), (12*60, 12*60+30)],
    2: [(11*60+30, 12*60), (13*60+30, 14*60), (15*60, 15*60+30)],
    3: [(9*60, 10*60), (11*60+30, 12*60), (16*60+30, 17*60)]
}

# Angela's busy intervals:
# Monday: 9:00-16:00
# Tuesday: 9:00-10:00, 10:30-11:00, 11:30-12:00, 12:30-17:00
# Wednesday: 9:00-12:30, 13:00-13:30, 14:30-16:00
# Thursday: 9:00-10:30, 11:00-16:30
angela_busy = {
    0: [(9*60, 16*60)],
    1: [(9*60, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 17*60)],
    2: [(9*60, 12*60+30), (13*60, 13*60+30), (14*60+30, 16*60)],
    3: [(9*60, 10*60+30), (11*60, 16*60+30)]
}

# Utility function: The meeting (starting at time s) should not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes after midnight

        # The meeting must lie completely within the work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Danielle's busy constraints for the day.
        for busy_start, busy_end in danielle_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Add Angela's busy constraints for the day.
        for busy_start, busy_end in angela_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Check every possible start minute within the allowed period.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()

    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

if selected_day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    selected_end = selected_start + duration
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
        day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")