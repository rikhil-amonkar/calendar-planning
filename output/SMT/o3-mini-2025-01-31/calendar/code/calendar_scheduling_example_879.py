from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 in minutes (540)
WORK_END   = 17 * 60    # 17:00 in minutes (1020)

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Busy schedules (times in minutes from midnight)

# Jack's busy schedule:
# Monday: 13:30-14:00, 15:30-16:00
# Tuesday: 9:30-11:00, 12:00-12:30, 16:00-16:30
# Wednesday: 12:00-13:00, 13:30-14:30, 15:00-15:30
# Thursday: 9:00-10:00, 12:00-12:30, 14:30-15:00
jack_busy = {
    0: [ (13*60 + 30, 14*60),     # Monday: 13:30-14:00 -> (810,840)
         (15*60 + 30, 16*60)      # Monday: 15:30-16:00 -> (930,960)
       ],
    1: [ (9*60 + 30, 11*60),      # Tuesday: 9:30-11:00 -> (570,660)
         (12*60, 12*60 + 30),     # Tuesday: 12:00-12:30 -> (720,750)
         (16*60, 16*60 + 30)      # Tuesday: 16:00-16:30 -> (960,990)
       ],
    2: [ (12*60, 13*60),         # Wednesday: 12:00-13:00 -> (720,780)
         (13*60 + 30, 14*60 + 30), # Wednesday: 13:30-14:30 -> (810,870)
         (15*60, 15*60 + 30)       # Wednesday: 15:00-15:30 -> (900,930)
       ],
    3: [ (9*60, 10*60),          # Thursday: 9:00-10:00 -> (540,600)
         (12*60, 12*60 + 30),     # Thursday: 12:00-12:30 -> (720,750)
         (14*60 + 30, 15*60)      # Thursday: 14:30-15:00 -> (870,900)
       ]
}

# Gerald's busy schedule:
# Monday: 9:00-10:30, 11:00-13:30, 14:00-15:00, 15:30-16:30
# Tuesday: 9:00-13:30, 14:00-17:00
# Wednesday: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:00-17:00
# Thursday: 9:00-12:30, 13:00-16:00, 16:30-17:00
gerald_busy = {
    0: [ (9*60, 10*60 + 30),     # Monday: 9:00-10:30 -> (540,630)
         (11*60, 13*60 + 30),    # Monday: 11:00-13:30 -> (660,810)
         (14*60, 15*60),         # Monday: 14:00-15:00 -> (840,900)
         (15*60 + 30, 16*60 + 30) # Monday: 15:30-16:30 -> (930,990)
       ],
    1: [ (9*60, 13*60 + 30),     # Tuesday: 9:00-13:30 -> (540,810)
         (14*60, 17*60)          # Tuesday: 14:00-17:00 -> (840,1020)
       ],
    2: [ (9*60, 9*60 + 30),      # Wednesday: 9:00-9:30 -> (540,570)
         (10*60, 10*60 + 30),    # Wednesday: 10:00-10:30 -> (600,630)
         (11*60, 11*60 + 30),    # Wednesday: 11:00-11:30 -> (660,690)
         (12*60, 17*60)         # Wednesday: 12:00-17:00 -> (720,1020)
       ],
    3: [ (9*60, 12*60 + 30),     # Thursday: 9:00-12:30 -> (540,750)
         (13*60, 16*60),         # Thursday: 13:00-16:00 -> (780,960)
         (16*60 + 30, 17*60)      # Thursday: 16:30-17:00 -> (990,1020)
       ]
}

# Utility function to ensure that a meeting starting at 's' does not overlap
# with a busy interval [busy_start, busy_end). Overlap is not allowed if:
# meeting_end > busy_start and meeting_start < busy_end.
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Enforce working hours constraint.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Jack's busy constraints for this day.
        for busy_start, busy_end in jack_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # Add Gerald's busy constraints for this day.
        for busy_start, busy_end in gerald_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # For earliest availability, try every minute from WORK_START to latest possible start.
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
    start_h, start_m = divmod(selected_start, 60)
    end_h, end_m = divmod(selected_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_h, start_m, end_h, end_m))
else:
    print("No valid meeting time could be found that satisfies all constraints.")