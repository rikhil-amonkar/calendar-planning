from z3 import *

# Meeting parameters
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END   = 17 * 60  # 17:00 in minutes
DURATION   = 60       # 1 hour

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Busy intervals per participant per day (minutes from 00:00)
# Format: { day_index: [(start_min, end_min), ...], ... }
natalie_busy = {
    0: [  # Monday
        (540, 570), (600, 720), (750, 780), (840, 870), (900, 990)
    ],
    1: [  # Tuesday
        (540, 570), (600, 630), (750, 840), (960, 1020)
    ],
    2: [  # Wednesday
        (660, 690), (960, 990)
    ],
    3: [  # Thursday
        (600, 660), (690, 900), (930, 960), (990, 1020)
    ]
}

william_busy = {
    0: [  # Monday
        (570, 660), (690, 1020)
    ],
    1: [  # Tuesday
        (540, 780), (810, 960)
    ],
    2: [  # Wednesday
        (540, 750), (780, 870), (930, 960), (990, 1020)
    ],
    3: [  # Thursday
        (540, 630), (660, 690), (720, 750), (780, 840), (900, 1020)
    ]
}

# Z3 variables
day = Int('day')       # 0=Mon, 1=Tue, 2=Wed, 3=Thu
start = Int('start')   # start time in minutes since 00:00
end = start + DURATION

opt = Optimize()
opt.add(day >= 0, day <= 3)
opt.add(start >= WORK_START, end <= WORK_END)

# Optional: align meeting start to 30-minute increments
opt.add(start % 30 == 0)

# No overlap constraints for each participant per selected day
for d in range(4):
    # Natalie
    for (bs, be) in natalie_busy.get(d, []):
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))
    # William
    for (bs, be) in william_busy.get(d, []):
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))

# Prefer earliest day, then earliest time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    day_idx = m[day].as_long()
    st = m[start].as_long()
    en = st + DURATION

    def mm_to_str(t):
        h = t // 60
        m_ = t % 60
        return f"{h:02d}:{m_:02d}"

    start_str = mm_to_str(st)
    end_str = mm_to_str(en)

    # Output day and time range in required format
    print(days[day_idx])
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No solution found.")