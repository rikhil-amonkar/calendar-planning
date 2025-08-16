from z3 import Optimize, Int, And, Or, Implies

def min_to_time(m):
    # m is minutes after 09:00
    hour = 9 + (m // 60)
    minute = m % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    DURATION = 30  # minutes
    WORK_START = 0          # 09:00 as 0 minutes
    WORK_END = 8 * 60       # 17:00 as 480 minutes
    LAST_START = WORK_END - DURATION

    # Blocked intervals in minutes after 09:00 for each participant per day
    # Format: { day_index: [(start, end), ...], ... }
    mary_blocks = {
        0: [],  # Monday
        1: [(60, 90), (390, 420)],               # Tuesday: 10:00-10:30, 15:30-16:00
        2: [(30, 60), (360, 390)],               # Wednesday: 09:30-10:00, 15:00-15:30
        3: [(0, 60), (90, 150)],                 # Thursday: 09:00-10:00, 10:30-11:30
    }
    alexis_blocks = {
        0: [(0, 60), (90, 180), (210, 450)],     # Monday: 09:00-10:00, 10:30-12:00, 12:30-16:30
        1: [(0, 60), (90, 150), (180, 390), (420, 480)],  # Tuesday: 09-10, 10:30-11:30, 12-15:30, 16-17
        2: [(0, 120), (150, 480)],               # Wednesday: 09:00-11:00, 11:30-17:00
        3: [(60, 180), (300, 330), (390, 420), (450, 480)],  # Thursday: 10-12, 14-14:30, 15:30-16, 16:30-17
    }

    # Decision variables
    day = Int('day')
    start = Int('start')
    end = Int('end')

    opt = Optimize()
    opt.set(priority='lex')  # minimize day first, then start

    # Basic bounds
    opt.add(day >= 0, day <= 3)
    opt.add(start >= WORK_START, start <= LAST_START)
    opt.add(end == start + DURATION)

    # Non-overlap constraints for each participant per day
    def non_overlap_constraints(blocks):
        cons = []
        for (bs, be) in blocks:
            cons.append(Or(end <= bs, start >= be))
        return And(cons) if cons else And()  # And() with no args is True

    for d in range(4):
        opt.add(Implies(day == d, non_overlap_constraints(mary_blocks.get(d, []))))
        opt.add(Implies(day == d, non_overlap_constraints(alexis_blocks.get(d, []))))

    # Optimize for earliest availability: earliest day, then earliest start time
    opt.minimize(day)
    opt.minimize(start)

    if opt.check() !=  sat:
        raise RuntimeError("No solution found, but problem statement guarantees one.")

    m = opt.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + DURATION

    print("SOLUTION:")
    print(f"Day: {day_names[d_val]}")
    print(f"Start Time: {min_to_time(s_val)}")
    print(f"End Time: {min_to_time(e_val)}")

if __name__ == "__main__":
    main()