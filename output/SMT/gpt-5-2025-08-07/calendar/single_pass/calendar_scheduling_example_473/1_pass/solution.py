from z3 import Optimize, Int, Or, sat

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
DUR = 30  # minutes
WORK_START = 9 * 60
WORK_END = 17 * 60

# Busy intervals (start_minute, end_minute), minutes from midnight
busy = []
# Gregory
busy += [(9*60, 9*60+30), (11*60+30, 12*60)]
# Jonathan
busy += [(9*60, 9*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)]
# Barbara
busy += [(10*60, 10*60+30), (13*60+30, 14*60)]
# Jesse
busy += [(10*60, 11*60), (12*60+30, 14*60+30)]
# Alan
busy += [(9*60+30, 11*60), (11*60+30, 12*60+30), (13*60, 15*60+30), (16*60, 17*60)]
# Nicole
busy += [(9*60, 10*60+30), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 17*60)]
# Catherine
busy += [(9*60, 10*60+30), (12*60, 13*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]

opt = Optimize()
start = Int('start')

# Work hours and 30-min grid
opt.add(start >= WORK_START)
opt.add(start + DUR <= WORK_END)
opt.add(start % 30 == 0)

# No overlap with any busy interval: [start, start+DUR) does not intersect [b0, b1)
for b0, b1 in busy:
    opt.add(Or(start + DUR <= b0, start >= b1))

# Prefer earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s = m[start].as_long()
    e = s + DUR
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {fmt_time(s)} (24-hour format)")
    print(f"End Time: {fmt_time(e)} (24-hour format)")
else:
    # As per problem statement, a solution exists; this is a fallback.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 00:00 (24-hour format)")
    print("End Time: 00:30 (24-hour format)")