from z3 import *

# Meeting parameters
duration = 30  # minutes
work_start = 9 * 60   # 09:00 in minutes
work_end   = 17 * 60  # 17:00 in minutes

# Days
days = ["Monday", "Tuesday", "Wednesday"]
DAYS = range(3)

# Busy schedules: times are in minutes since 00:00
def t(h, m=0): return h * 60 + m

nancy_busy = {
    0: [  # Monday
        (t(10,0), t(10,30)),
        (t(11,30), t(12,30)),
        (t(13,30), t(14,0)),
        (t(14,30), t(15,30)),
        (t(16,0), t(17,0))
    ],
    1: [  # Tuesday
        (t(9,30), t(10,30)),
        (t(11,0), t(11,30)),
        (t(12,0), t(12,30)),
        (t(13,0), t(13,30)),
        (t(15,30), t(16,0))
    ],
    2: [  # Wednesday
        (t(10,0), t(11,30)),
        (t(13,30), t(16,0))
    ]
}

jose_busy = {
    0: [  # Monday
        (t(9,0), t(17,0))
    ],
    1: [  # Tuesday
        (t(9,0), t(17,0))
    ],
    2: [  # Wednesday
        (t(9,0),  t(9,30)),
        (t(10,0), t(12,30)),
        (t(13,30), t(14,30)),
        (t(15,0),  t(17,0))
    ]
}

# Z3 variables
day = Int('day')      # 0=Mon, 1=Tue, 2=Wed
start = Int('start')  # minutes since 00:00 for the chosen day

o = Optimize()

# Domain constraints
o.add(And(day >= 0, day <= 2))
o.add(And(start >= work_start, start + duration <= work_end))

# Non-overlap constraints for each participant
def no_overlap(busy_map):
    for d in DAYS:
        for (s, e) in busy_map[d]:
            # Meeting [start, start+duration) must not intersect [s, e)
            o.add(Implies(day == d, Or(start >= e, start + duration <= s)))

no_overlap(nancy_busy)
no_overlap(jose_busy)

# Earliest availability: minimize day first, then start time
o.minimize(day)
o.minimize(start)

if o.check() == sat:
    m = o.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + duration

    def fmt(mm):
        h = mm // 60
        m_ = mm % 60
        return f"{h:02d}:{m_:02d}"

    day_str = days[d_val]
    print(f"{day_str} {{{fmt(s_val)}:{fmt(e_val)}}}")
else:
    print("No solution found")