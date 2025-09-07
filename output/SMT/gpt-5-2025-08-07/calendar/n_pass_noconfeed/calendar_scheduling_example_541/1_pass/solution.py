from z3 import *

def to_minutes(h, m=0):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def no_overlap(s, e, bs, be):
    # Meeting [s, e) does not overlap block [bs, be)
    return Or(e <= bs, s >= be)

def main():
    # Problem setup
    day = "Monday"
    work_start = to_minutes(9, 0)
    work_end = to_minutes(17, 0)
    duration = 60  # 1 hour

    # Participants' blocked times (in minutes since 00:00)
    kayla_blocks = [
        (to_minutes(10, 0), to_minutes(10, 30)),
        (to_minutes(14, 30), to_minutes(16, 0)),
    ]
    rebecca_blocks = [
        (to_minutes(9, 0), to_minutes(13, 0)),
        (to_minutes(13, 30), to_minutes(15, 0)),
        (to_minutes(15, 30), to_minutes(16, 0)),
    ]

    # Z3 model
    start, end = Ints('start end')
    opt = Optimize()

    # Meeting duration and within working hours
    opt.add(end == start + duration)
    opt.add(start >= work_start, end <= work_end)

    # No overlap with Kayla's blocks
    for bs, be in kayla_blocks:
        opt.add(no_overlap(start, end, bs, be))

    # No overlap with Rebecca's blocks
    for bs, be in rebecca_blocks:
        opt.add(no_overlap(start, end, bs, be))

    # Prefer earliest feasible time
    opt.minimize(start)

    if opt.check() == sat:
        m = opt.model()
        s_val = m[start].as_long()
        e_val = m[end].as_long()
        time_range = f"{fmt_time(s_val)}:{fmt_time(e_val)}"
        print(f"{day} {{{time_range}}}")
    else:
        print("No feasible meeting time found.")

if __name__ == "__main__":
    main()