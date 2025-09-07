from z3 import *

def minutes(h, m):
    return h * 60 + m

def format_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}

# Work hours
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 60  # 1 hour

# Blocked intervals per person per day: [start, end) in minutes since midnight
martha_blocks = {
    0: [(minutes(16, 0), minutes(17, 0))],
    1: [(minutes(15, 0), minutes(15, 30))],
    2: [(minutes(10, 0), minutes(11, 0)), (minutes(14, 0), minutes(14, 30))]
}

beverly_blocks = {
    0: [(minutes(9, 0), minutes(13, 30)), (minutes(14, 0), minutes(17, 0))],
    1: [(minutes(9, 0), minutes(17, 0))],
    2: [(minutes(9, 30), minutes(15, 30)), (minutes(16, 30), minutes(17, 0))]
}

# Initialize solver
s = Solver()

day = Int('day')
start = Int('start')
end = Int('end')

# Basic constraints
s.add(Or(day == 0, day == 1, day == 2))
s.add(start >= work_start, end == start + duration, end <= work_end)

# Optional: enforce 30-minute granularity
s.add(start % 30 == 0)

# No overlap helper: (end <= bstart) or (start >= bend)
def no_overlap_with_blocks(blocks, who_name):
    for d, intervals in blocks.items():
        for (bs, be) in intervals:
            s.add(Or(day != d, end <= bs, start >= be))

# Apply constraints for both participants
no_overlap_with_blocks(martha_blocks, "Martha")
no_overlap_with_blocks(beverly_blocks, "Beverly")

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    en = m[end].as_long()
    print(f"{day_names[d]} {{{format_time(st)}:{format_time(en)}}}")
else:
    print("No solution found.")