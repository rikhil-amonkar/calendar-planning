from z3 import *

def minutes_to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def main():
    # Problem setup
    day = "Monday"
    work_start = 9 * 60       # 09:00
    work_end = 17 * 60        # 17:00
    duration = 30             # 30 minutes

    # Albert's blocked times on Monday (start, end) in minutes
    albert_blocks = [
        (9 * 60, 10 * 60),      # 09:00-10:00
        (10 * 60 + 30, 12 * 60),# 10:30-12:00
        (15 * 60, 16 * 60 + 30) # 15:00-16:30
    ]

    # SMT variables
    start = Int("start")
    end = Int("end")

    opt = Optimize()

    # Basic meeting constraints
    opt.add(end - start == duration)
    opt.add(start >= work_start, end <= work_end)

    # Deborah is free all day -> no additional constraints for Deborah

    # Albert cannot meet after 11:00 on Monday -> meeting must end by 11:00
    opt.add(end <= 11 * 60)

    # Avoid Albert's blocked intervals
    for (b_start, b_end) in albert_blocks:
        opt.add(Or(end <= b_start, start >= b_end))

    # Optional: choose the earliest valid meeting
    opt.minimize(start)

    if opt.check() != sat:
        print("No feasible meeting found.")
        return

    model = opt.model()
    s = model[start].as_long()
    e = model[end].as_long()

    time_range = "{" + f"{minutes_to_hhmm(s)}:{minutes_to_hhmm(e)}" + "}"
    print(day)
    print(time_range)

if __name__ == "__main__":
    main()