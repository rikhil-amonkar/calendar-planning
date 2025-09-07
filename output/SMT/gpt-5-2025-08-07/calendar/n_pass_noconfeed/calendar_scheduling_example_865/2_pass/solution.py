from z3 import Optimize, Int, Or, And, sat

# Meeting parameters
DURATION = 60  # minutes
WORK_BLOCK = 8 * 60  # 09:00-17:00 => 480 minutes

# Day indices: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Busy intervals per participant per day, in minutes from 09:00 of that day
busy = {
    'Megan': {
        0: [(240, 270), (300, 390)],                     # Monday: 13:00-13:30, 14:00-15:30
        1: [(0, 30), (180, 210), (420, 480)],            # Tuesday: 9:00-9:30, 12:00-12:30, 16:00-17:00
        2: [(30, 60), (90, 150), (210, 300), (420, 450)],# Wednesday: 9:30-10:00, 10:30-11:30, 12:30-14:00, 16:00-16:30
        3: [(270, 330), (360, 390)]                      # Thursday: 13:30-14:30, 15:00-15:30
    },
    'Daniel': {
        0: [(60, 150), (210, 360)],                      # Monday: 10:00-11:30, 12:30-15:00
        1: [(0, 60), (90, 480)],                         # Tuesday: 9:00-10:00, 10:30-17:00
        2: [(0, 60), (90, 150), (180, 480)],             # Wednesday: 9:00-10:00, 10:30-11:30, 12:00-17:00
        3: [(0, 180), (210, 330), (360, 390), (420, 480)]# Thursday: 9:00-12:00, 12:30-14:30, 15:00-15:30, 16:00-17:00
    }
}

# Z3 variables
day = Int('day')          # which day (0..3)
start = Int('start')      # minutes from 09:00 within that day

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 3))
opt.add(And(start >= 0, start + DURATION <= WORK_BLOCK))

# Non-overlap constraints with all participants' busy intervals
end = start + DURATION
for person in busy:
    for d_idx, intervals in busy[person].items():
        for (bs, be) in intervals:
            # If the meeting is on day d_idx, it must not overlap [bs, be)
            opt.add(Or(day != d_idx, end <= bs, start >= be))

# Minimize earliest absolute start across the week
absolute_start = day * WORK_BLOCK + start
opt.minimize(absolute_start)

# Solve
res = opt.check()
if res != sat:
    print("No solution found")
else:
    m = opt.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + DURATION

    def fmt_time(mins_from_9):
        h = 9 + mins_from_9 // 60
        mm = mins_from_9 % 60
        return f"{h:02d}:{mm:02d}"

    start_str = fmt_time(s_val)
    end_str = fmt_time(e_val)

    print(day_names[d_val])
    print("{" + start_str + ":" + end_str + "}")