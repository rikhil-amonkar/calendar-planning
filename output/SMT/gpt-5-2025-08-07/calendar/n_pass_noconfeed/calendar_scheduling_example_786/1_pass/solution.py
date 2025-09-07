from z3 import Optimize, Int, Or, And

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60   # 09:00 -> 540
WORK_END   = 17 * 60  # 17:00 -> 1020
LAST_START = WORK_END - DURATION

# Day mapping: 0=Monday, 1=Tuesday, 2=Wednesday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}

# Z3 variables
day = Int('day')
start = Int('start')

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 2))
opt.add(And(start >= WORK_START, start <= LAST_START))

# Helper: add a "no-overlap" constraint for a busy interval on a given day
def no_overlap(d, b_start, b_end):
    # Meeting [start, start + DURATION) must not overlap [b_start, b_end)
    # Encode as: (day != d) OR (start + DURATION <= b_start) OR (start >= b_end)
    opt.add(Or(day != d, start + DURATION <= b_start, start >= b_end))

# Busy schedules (minutes from midnight)
# Amy
# Wednesday: 11:00-11:30, 13:30-14:00
no_overlap(2, 11*60, 11*60 + 30)
no_overlap(2, 13*60 + 30, 14*60)

# Pamela
# Monday: 9:00-10:30, 11:00-16:30
no_overlap(0, 9*60, 10*60 + 30)
no_overlap(0, 11*60, 16*60 + 30)

# Tuesday: 9:00-9:30, 10:00-17:00
no_overlap(1, 9*60, 9*60 + 30)
no_overlap(1, 10*60, 17*60)

# Wednesday: 9:00-9:30, 10:00-11:00, 11:30-13:30, 14:30-15:00, 16:00-16:30
no_overlap(2, 9*60, 9*60 + 30)
no_overlap(2, 10*60, 11*60)
no_overlap(2, 11*60 + 30, 13*60 + 30)
no_overlap(2, 14*60 + 30, 15*60)
no_overlap(2, 16*60, 16*60 + 30)

# Preferences (soft constraints):
# Pamela would like to avoid more meetings on Monday, Tuesday, and Wednesday before 16:00.
opt.add_soft(day != 0, weight='10')  # Avoid Monday
opt.add_soft(day != 1, weight='10')  # Avoid Tuesday
opt.add_soft(Or(day != 2, start >= 16*60), weight='5')  # If Wednesday, prefer start >= 16:00

# Solve
if opt.check() != None:
    model = opt.model()
    dval = model.eval(day).as_long()
    sval = model.eval(start).as_long()
    eval_ = sval + DURATION

    def fmt(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"

    day_str = day_names[dval]
    start_str = fmt(sval)
    end_str = fmt(eval_)

    # Output format must include day and time range like {HH:MM:HH:MM}
    print(f"{day_str} {{{start_str}:{end_str}}}")