from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 in minutes (540)
WORK_END   = 17 * 60    # 17:00 in minutes (1020)

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Alan does not want to meet on Tuesday, Wednesday, or Thursday,
# and on Monday he only accepts meetings starting at or after 16:30.
# Therefore, our candidate day is Monday only.
candidate_days = [0]

# Define busy schedules in minutes.
# Janet's busy schedule:
janet_busy = {
    0: [ (11 * 60 + 30, 12 * 60),    # Monday: 11:30-12:00  -> (690,720)
         (12 * 60 + 30, 13 * 60)     # Monday: 12:30-13:00  -> (750,780)
       ],
    1: [ (11 * 60, 12 * 60 + 30),    # Tuesday: 11:00-12:30 -> (660,750)
         (14 * 60, 14 * 60 + 30),    # Tuesday: 14:00-14:30 -> (840,870)
         (16 * 60, 16 * 60 + 30)     # Tuesday: 16:00-16:30 -> (960,990)
       ],
    2: [ (11 * 60, 11 * 60 + 30),    # Wednesday: 11:00-11:30 -> (660,690)
         (13 * 60, 14 * 60),         # Wednesday: 13:00-14:00 -> (780,840)
         (14 * 60 + 30, 15 * 60),    # Wednesday: 14:30-15:00 -> (870,900)
         (16 * 60 + 30, 17 * 60)     # Wednesday: 16:30-17:00 -> (990,1020)
       ],
    3: [ (10 * 60, 11 * 60),        # Thursday: 10:00-11:00 -> (600,660)
         (11 * 60 + 30, 12 * 60),    # Thursday: 11:30-12:00 -> (690,720)
         (13 * 60 + 30, 14 * 60 + 30),# Thursday: 13:30-14:30 -> (810,870)
         (15 * 60, 15 * 60 + 30)     # Thursday: 15:00-15:30 -> (900,930)
       ]
}

# Alan's busy schedule:
alan_busy = {
    0: [ (9 * 60, 10 * 60 + 30),    # Monday: 9:00-10:30  -> (540,630)
         (11 * 60 + 30, 12 * 60 + 30),# Monday: 11:30-12:30 -> (690,750)
         (13 * 60 + 30, 14 * 60),    # Monday: 13:30-14:00 -> (810,840)
         (15 * 60 + 30, 16 * 60 + 30) # Monday: 15:30-16:30 -> (930,990)
       ],
    1: [ (9 * 60, 9 * 60 + 30),      # Tuesday: 9:00-9:30   -> (540,570)
         (10 * 60 + 30, 11 * 60 + 30),# Tuesday: 10:30-11:30 -> (630,690)
         (12 * 60 + 30, 13 * 60),    # Tuesday: 12:30-13:00 -> (750,780)
         (14 * 60, 15 * 60 + 30),    # Tuesday: 14:00-15:30 -> (840,930)
         (16 * 60, 17 * 60)         # Tuesday: 16:00-17:00 -> (960,1020)
       ],
    2: [ (9 * 60, 9 * 60 + 30),      # Wednesday: 9:00-9:30  -> (540,570)
         (11 * 60 + 30, 12 * 60 + 30),# Wednesday: 11:30-12:30 -> (690,750)
         (13 * 60 + 30, 14 * 60 + 30),# Wednesday: 13:30-14:30 -> (810,870)
         (15 * 60, 15 * 60 + 30)     # Wednesday: 15:00-15:30 -> (900,930)
       ],
    3: [ (9 * 60, 10 * 60),         # Thursday: 9:00-10:00  -> (540,600)
         (10 * 60 + 30, 11 * 60),    # Thursday: 10:30-11:00 -> (630,660)
         (11 * 60 + 30, 12 * 60),    # Thursday: 11:30-12:00 -> (690,720)
         (13 * 60, 14 * 60),         # Thursday: 13:00-14:00 -> (780,840)
         (14 * 60 + 30, 15 * 60),    # Thursday: 14:30-15:00 -> (870,900)
         (15 * 60 + 30, 16 * 60 + 30) # Thursday: 15:30-16:30 -> (930,990)
       ]
}

# Additional preference: On Monday, Alan does not want to meet before 16:30.
# 16:30 in minutes is:
MONDAY_MIN_START = 16 * 60 + 30  # 16:30 -> 990

# Utility function: For a meeting start time 's' (with given duration),
# ensure it does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Enforce working hours constraint.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # For Monday, enforce Alan's preference
        if day == 0:
            solver.add(s >= MONDAY_MIN_START)

        # Add Janet's busy constraints.
        for busy_start, busy_end in janet_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Add Alan's busy constraints.
        for busy_start, busy_end in alan_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))

        # Since we require the earliest meeting time, try each minute from WORK_START to latest possible start.
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
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")