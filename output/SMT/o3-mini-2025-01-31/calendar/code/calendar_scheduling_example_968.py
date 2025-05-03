from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30               # 30 minutes meeting
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map numeric day to day names: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# ---------------------------
# Hard constraints: available slots
# Catherine is completely free, so no blocked intervals.
# Debra's blocked times (hard constraints)
debra_busy = {
    0: [  # Monday
        (9 * 60, 13 * 60 + 30),   # 9:00 to 13:30
        (14 * 60, 16 * 60),       # 14:00 to 16:00
        (16 * 60 + 30, 17 * 60)    # 16:30 to 17:00
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30
        (10 * 60 + 30, 11 * 60 + 30), # 10:30 to 11:30
        (12 * 60, 14 * 60),       # 12:00 to 14:00
        (14 * 60 + 30, 15 * 60),  # 14:30 to 15:00
        (15 * 60 + 30, 16 * 60 + 30) # 15:30 to 16:30
    ],
    2: [  # Wednesday
        (9 * 60, 11 * 60),        # 9:00 to 11:00
        (11 * 60 + 30, 17 * 60)    # 11:30 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30
        (10 * 60, 16 * 60 + 30)   # 10:00 to 16:30
    ],
    4: [  # Friday
        (9 * 60, 11 * 60),        # 9:00 to 11:00
        (11 * 60 + 30, 17 * 60)    # 11:30 to 17:00
    ]
}

# ---------------------------
# Preferences (soft constraints):
# Catherine would rather not meet on Wednesday (d==2) or Friday (d==4).
# Debra would like to avoid more meetings on:
#   Monday (d==0),
#   Tuesday after 11:00 (d==1 and s >= 11*60),
#   Thursday (d==3).
#
# We will add a penalty (cost) for these preferences and use Optimize to minimize it.
def compute_penalty(d, s):
    penalty = 0
    penalty += If(d == 2, 1, 0)   # Catherine avoids Wednesday
    penalty += If(d == 4, 1, 0)   # Catherine avoids Friday
    penalty += If(d == 0, 1, 0)   # Debra avoids Monday
    penalty += If(And(d == 1, s >= 11 * 60), 1, 0)  # Debra avoids Tuesday after 11:00
    penalty += If(d == 3, 1, 0)   # Debra avoids Thursday
    return penalty

# Helper: Non overlapping constraint: meeting [s, s+duration) must not overlap with busy [bstart, bend)
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create an optimizer instance
opt = Optimize()

# Create variables: d for day (0-4) and s for meeting start time (in minutes from midnight)
d = Int("d")
s = Int("s")

# Day must be between 0 (Monday) and 4 (Friday)
opt.add(d >= 0, d <= 4)

# Meeting must be within work hours
opt.add(s >= WORK_START, s + duration <= WORK_END)

# Hard constraints: Debra's busy times. For the chosen day, ensure no overlap.
for day in debra_busy:
    for (bstart, bend) in debra_busy[day]:
        # If the meeting is scheduled on 'day', then meeting must not overlap with [bstart, bend)
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add soft constraint objective: minimize the penalty for preferences.
penalty = compute_penalty(d, s)
h = opt.minimize(penalty)

# For earliest meeting time, we can add another objective: 
# minimize (d * (WORK_END) + s) ensures earlier days and earlier times.
# Multiply day by maximum minutes in a day to get primary order.
earliest_expr = d * (WORK_END) + s
h2 = opt.minimize(earliest_expr)

if opt.check() == sat:
    model = opt.model()
    meeting_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration
    start_hour, start_minute = divmod(meeting_start, 60)
    end_hour, end_minute = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[meeting_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time found that satisfies all constraints.")