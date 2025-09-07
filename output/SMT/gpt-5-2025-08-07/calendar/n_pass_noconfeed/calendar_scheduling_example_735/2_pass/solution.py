from z3 import Optimize, Int, Or, sat

# Meeting parameters
MEETING_DURATION = 30  # minutes
WORK_START = 9 * 60    # 09:00 in minutes from midnight
WORK_END = 17 * 60     # 17:00 in minutes from midnight
DAY_NAMES = ["Monday", "Tuesday", "Wednesday"]

# We model time within the work window as minutes since 09:00 (0 to 480)
DAY_RANGE = range(3)  # 0: Monday, 1: Tuesday, 2: Wednesday
DAY_MINUTES = WORK_END - WORK_START  # 480

# Helper to convert "HH:MM" to minutes since 09:00
def t(h, m):
    return (h * 60 + m) - WORK_START

# Blocked intervals per person: (day_index, start_min_since_09, end_min_since_09)
ronald_blocks = [
    # Monday
    (0, t(10, 30), t(11, 0)),
    (0, t(12, 0),  t(12, 30)),
    (0, t(15, 30), t(16, 0)),
    # Tuesday
    (1, t(9, 0),   t(9, 30)),
    (1, t(12, 0),  t(12, 30)),
    (1, t(15, 30), t(16, 30)),
    # Wednesday
    (2, t(9, 30),  t(10, 30)),
    (2, t(11, 0),  t(12, 0)),
    (2, t(12, 30), t(13, 0)),
    (2, t(13, 30), t(14, 0)),
    (2, t(16, 30), t(17, 0)),
]

amber_blocks = [
    # Monday
    (0, t(9, 0),   t(9, 30)),
    (0, t(10, 0),  t(10, 30)),
    (0, t(11, 30), t(12, 0)),
    (0, t(12, 30), t(14, 0)),
    (0, t(14, 30), t(15, 0)),
    (0, t(15, 30), t(17, 0)),
    # Tuesday
    (1, t(9, 0),   t(9, 30)),
    (1, t(10, 0),  t(11, 30)),
    (1, t(12, 0),  t(12, 30)),
    (1, t(13, 30), t(15, 30)),
    (1, t(16, 30), t(17, 0)),
    # Wednesday
    (2, t(9, 0),   t(9, 30)),
    (2, t(10, 0),  t(10, 30)),
    (2, t(11, 0),  t(13, 30)),
    (2, t(15, 0),  t(15, 30)),
]

# Z3 variables
opt = Optimize()
opt.set('opt.priority', 'lex')  # Minimize lexicographically: day, then start

day = Int('day')       # 0..2 for Mon..Wed
start = Int('start')   # 0..480 minutes since 09:00
end = Int('end')

# Basic constraints
opt.add(day >= 0, day <= 2)
opt.add(start >= 0, end == start + MEETING_DURATION, end <= DAY_MINUTES)

# Align to 30-minute grid
opt.add(start % 30 == 0)

# Non-overlap constraints: for each block, if day matches then meeting must not overlap
def add_non_overlap(blocks):
    for d, s, e in blocks:
        opt.add(Or(day != d, end <= s, start >= e))

add_non_overlap(ronald_blocks)
add_non_overlap(amber_blocks)

# Minimize earliest day, then earliest start time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + MEETING_DURATION

    # Convert back to absolute HH:MM
    def to_hhmm(minutes_since_9):
        total = WORK_START + minutes_since_9
        hh = total // 60
        mm = total % 60
        return f"{hh:02d}:{mm:02d}"

    s_str = to_hhmm(s_val)
    e_str = to_hhmm(e_val)
    print(f"{DAY_NAMES[d_val]} {{{s_str}:{e_str}}}")
else:
    print("No feasible meeting time found.")