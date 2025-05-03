from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 in minutes
WORK_END   = 17 * 60    # 17:00 in minutes

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Additional non-meeting constraints:
# • Evelyn cannot meet on Monday before 16:30 and is not available on Tuesday.
# • Dylan cannot meet on Wednesday or Thursday.
# Therefore, the only candidate day for both is Monday.
candidate_days = [0]

# Busy schedules (times in minutes from midnight)

# Evelyn's busy schedule:
# Monday: 9:30-10:00, 10:30-11:00, 11:30-12:00, 13:00-15:00
# Tuesday: 10:00-11:00, 12:00-14:00, 15:00-15:30, 16:00-17:00
# Wednesday: 9:00-10:30, 13:30-16:00
# Thursday: 9:30-10:00, 11:00-12:00, 12:30-13:00, 15:30-16:30
evelyn_busy = {
    0: [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (13*60, 15*60)],
    1: [(10*60, 11*60), (12*60, 14*60), (15*60, 15*60+30), (16*60, 17*60)],
    2: [(9*60, 10*60+30), (13*60+30, 16*60)],
    3: [(9*60+30, 10*60), (11*60, 12*60), (12*60+30, 13*60), (15*60+30, 16*60+30)]
}

# Dylan's busy schedule:
# Monday: 9:00-9:30, 10:30-11:00, 13:00-13:30, 14:00-14:30, 15:30-16:30
# Tuesday: 9:00-13:00, 13:30-14:00, 14:30-17:00
# Wednesday: 9:00-10:30, 11:00-12:30, 13:00-14:00, 14:30-15:00
# Thursday: 9:30-10:30, 11:30-12:00, 13:30-14:00, 14:30-17:00
dylan_busy = {
    0: [(9*60, 9*60+30), (10*60+30, 11*60), (13*60, 13*60+30), (14*60, 14*60+30), (15*60+30, 16*60+30)],
    1: [(9*60, 13*60), (13*60+30, 14*60), (14*60+30, 17*60)],
    2: [(9*60, 10*60+30), (11*60, 12*60+30), (13*60, 14*60), (14*60+30, 15*60)],
    3: [(9*60+30, 10*60+30), (11*60+30, 12*60), (13*60+30, 14*60), (14*60+30, 17*60)]
}

# Utility function: returns the Z3 constraint that ensures
# a meeting starting at time 's' (for the given duration)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    # No overlap if the meeting ends on or before the busy interval starts,
    # or starts on or after the busy interval ends.
    return Or(s + duration <= busy_start, s >= busy_end)

# Find an available meeting time on one of the candidate days
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes from midnight)
        
        # Meeting must be within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Additional constraint for Evelyn:
        # On Monday (day==0), she cannot meet before 16:30.
        if day == 0:
            solver.add(s >= 16*60 + 30)  # 16:30
        
        # Add Evelyn's busy time constraints for this day.
        for busy_start, busy_end in evelyn_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Dylan's busy time constraints for this day.
        for busy_start, busy_end in dylan_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Search for the earliest valid meeting time in minute increments.
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