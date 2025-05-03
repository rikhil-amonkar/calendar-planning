from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration in minutes (one hour)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END   = 17 * 60    # 17:00 → 1020 minutes

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# Due to preferences:
# - Vincent would rather not meet on Monday.
# - Benjamin would like to avoid more meetings on Wednesday.
# Thus, we prefer Tuesday (1) and Thursday (3) if possible.
candidate_days = [1, 3]

# Vincent's busy intervals in minutes after midnight:
vincent_busy = {
    0: [  # Monday
        (9*60, 9*60+30),     # 9:00 - 9:30
        (10*60, 11*60),      # 10:00 - 11:00
        (12*60, 13*60+30),   # 12:00 - 13:30
        (14*60+30, 15*60),   # 14:30 - 15:00
        (15*60+30, 17*60)    # 15:30 - 17:00
    ],
    1: [  # Tuesday
        (10*60, 13*60+30),   # 10:00 - 13:30
        (14*60, 14*60+30),   # 14:00 - 14:30
        (15*60, 17*60)       # 15:00 - 17:00
    ],
    2: [  # Wednesday
        (9*60, 11*60),       # 9:00 - 11:00
        (11*60+30, 12*60),    # 11:30 - 12:00
        (13*60, 13*60+30),    # 13:00 - 13:30
        (14*60, 16*60),       # 14:00 - 16:00
        (16*60+30, 17*60)     # 16:30 - 17:00
    ],
    3: [  # Thursday
        (9*60+30, 11*60),     # 9:30 - 11:00
        (11*60+30, 13*60),    # 11:30 - 13:00
        (13*60+30, 14*60+30),  # 13:30 - 14:30
        (15*60, 16*60),       # 15:00 - 16:00
        (16*60+30, 17*60)     # 16:30 - 17:00
    ]
}

# Benjamin's calendar is wide open, so no busy intervals need to be added.

# Utility function: meeting starting at 's' should not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to scan through candidate days and find the earliest meeting time that meets all constraints.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")   # meeting start time in minutes after midnight

        # The meeting must lie completely within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Vincent's busy constraints for this day.
        for busy_start, busy_end in vincent_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Try every possible start minute from WORK_START to (WORK_END - duration) inclusively.
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
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")