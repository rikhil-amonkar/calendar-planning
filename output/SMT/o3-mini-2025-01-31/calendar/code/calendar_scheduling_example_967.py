from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60               # meeting duration in minutes (1 hour)
WORK_START = 9 * 60         # workday start: 9:00 (in minutes: 540)
WORK_END = 17 * 60          # workday end: 17:00 (in minutes: 1020)

# Mapping for day names: 0 -> Monday, 1 -> Tuesday, etc.
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals are represented as tuples (start, end) in minutes from midnight.
# Gregory's busy schedule
# For Monday, there is no busy time specified.
gregory_busy = {
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),           # 9:00 - 9:30
        (10 * 60 + 30, 11 * 60 + 30),      # 10:30 - 11:30
        (12 * 60, 12 * 60 + 30),           # 12:00 - 12:30
        (13 * 60, 13 * 60 + 30),           # 13:00 - 13:30
        (16 * 60, 16 * 60 + 30)            # 16:00 - 16:30
    ],
    2: [  # Wednesday
        (9 * 60, 12 * 60),                # 9:00 - 12:00
        (12 * 60 + 30, 13 * 60),           # 12:30 - 13:00
        (14 * 60, 14 * 60 + 30)            # 14:00 - 14:30
    ],
    3: [  # Thursday
        (9 * 60, 9 * 60 + 30),            # 9:00 - 9:30
        (11 * 60, 12 * 60 + 30),           # 11:00 - 12:30
        (13 * 60 + 30, 15 * 60),           # 13:30 - 15:00
        (16 * 60 + 30, 17 * 60)            # 16:30 - 17:00
    ],
    4: [  # Friday
        (9 * 60 + 30, 10 * 60),           # 9:30 - 10:00
        (11 * 60, 11 * 60 + 30),          # 11:00 - 11:30
        (12 * 60 + 30, 15 * 60),          # 12:30 - 15:00
        (16 * 60 + 30, 17 * 60)           # 16:30 - 17:00
    ]
}

# Adam's busy schedule
adam_busy = {
    0: [  # Monday
        (9 * 60, 11 * 60),               # 9:00 - 11:00
        (11 * 60 + 30, 16 * 60 + 30)      # 11:30 - 16:30
    ],
    1: [  # Tuesday
        (10 * 60, 11 * 60),              # 10:00 - 11:00
        (12 * 60, 13 * 60 + 30),         # 12:00 - 13:30
        (14 * 60, 15 * 60 + 30)          # 14:00 - 15:30
    ],
    2: [  # Wednesday
        (9 * 60 + 30, 10 * 60),          # 9:30 - 10:00
        (10 * 60 + 30, 12 * 60 + 30),     # 10:30 - 12:30
        (13 * 60, 15 * 60),              # 13:00 - 15:00
        (15 * 60 + 30, 16 * 60)          # 15:30 - 16:00
    ],
    3: [  # Thursday
        (9 * 60, 16 * 60 + 30)           # 9:00 - 16:30
    ],
    4: [  # Friday
        (9 * 60 + 30, 12 * 60),          # 9:30 - 12:00
        (12 * 60 + 30, 13 * 60),         # 12:30 - 13:00
        (13 * 60 + 30, 17 * 60)          # 13:30 - 17:00
    ]
}

def no_overlap(busy_start, busy_end, meeting_start, dur):
    # The meeting interval [meeting_start, meeting_start+dur) must not overlap with [busy_start, busy_end)
    return Or(meeting_start + dur <= busy_start, meeting_start >= busy_end)

def find_meeting_time():
    # Try each day in order from Monday (0) to Friday (4)
    for day in range(5):
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # The meeting must be fully within work hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Gregory's busy constraints for the day (if any)
        if day in gregory_busy:
            for busy_start, busy_end in gregory_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Adam's busy constraints for the day (if any)
        if day in adam_busy:
            for busy_start, busy_end in adam_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # To get the earliest possible meeting time, iterate through each possible start time from WORK_START onward.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()         # save the current state
            solver.add(s == t)    # fix start time to t
            if solver.check() == sat:
                model = solver.model()
                return day, model[s].as_long()
            solver.pop()          # backtrack if t doesn't work
    
    return None, None

day, start_time = find_meeting_time()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    sh, sm = divmod(start_time, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], sh, sm, eh, em))
else:
    print("No valid meeting time found that satisfies all constraints.")