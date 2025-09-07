from z3 import *

# Meeting parameters
day = "Monday"
duration = 30  # minutes
work_start = 9 * 60   # 09:00 in minutes since midnight
work_end   = 17 * 60  # 17:00 in minutes since midnight

# Helper to add non-overlap constraints
def no_overlap(opt, start_var, dur, a, b):
    # Meeting [start, start+dur) does not overlap busy [a, b)
    opt.add(Or(start_var + dur <= a, start_var >= b))

# Busy schedules (minutes since midnight)
busy = {
    "Jacob": [
        (13*60 + 30, 14*60 + 0),  # 13:30-14:00
        (14*60 + 30, 15*60 + 0),  # 14:30-15:00
    ],
    "Diana": [
        (9*60 + 30, 10*60 + 0),   # 09:30-10:00
        (11*60 + 30, 12*60 + 0),  # 11:30-12:00
        (13*60 + 0,  13*60 + 30), # 13:00-13:30
        (16*60 + 0,  16*60 + 30), # 16:00-16:30
    ],
    "Adam": [
        (9*60 + 30, 10*60 + 30),  # 09:30-10:30
        (11*60 + 0,  12*60 + 30), # 11:00-12:30
        (15*60 + 30, 16*60 + 0),  # 15:30-16:00
    ],
    "Angela": [
        (9*60 + 30, 10*60 + 0),   # 09:30-10:00
        (10*60 + 30, 12*60 + 0),  # 10:30-12:00
        (13*60 + 0,  15*60 + 30), # 13:00-15:30
        (16*60 + 0,  16*60 + 30), # 16:00-16:30
    ],
    "Dennis": [
        (9*60 + 0,  9*60 + 30),   # 09:00-09:30
        (10*60 + 30, 11*60 + 30), # 10:30-11:30
        (13*60 + 0,  15*60 + 0),  # 13:00-15:00
        (16*60 + 30, 17*60 + 0),  # 16:30-17:00
    ],
}

# Z3 variables
S = Int('S')  # start time in minutes since midnight

opt = Optimize()
# Within work hours
opt.add(S >= work_start, S + duration <= work_end)
# Align to half-hour boundaries for clean scheduling
opt.add(S % 30 == 0)

# Add non-overlap constraints for each participant
for person, intervals in busy.items():
    for (a, b) in intervals:
        no_overlap(opt, S, duration, a, b)

# Prefer the earliest feasible time
opt.minimize(S)

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

if opt.check() == sat:
    model = opt.model()
    start = model[S].as_long()
    end = start + duration
    print(day)
    print(f"{{{fmt(start)}:{fmt(end)}}}")
else:
    print("No feasible time found")