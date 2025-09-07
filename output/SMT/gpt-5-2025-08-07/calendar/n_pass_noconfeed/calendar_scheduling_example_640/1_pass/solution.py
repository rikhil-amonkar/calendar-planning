from z3 import Optimize, Int, Or, Implies

def no_overlap(start, dur, bstart, bend):
    return Or(start + dur <= bstart, start >= bend)

def minutes_to_hhmm(m):
    h = 9 + (m // 60)  # workday starts at 09:00
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    # Constants
    DURATION = 30  # minutes
    WORKDAY_MINUTES = 8 * 60  # 09:00 to 17:00

    # Day mapping: 0 = Monday, 1 = Tuesday
    day_names = {0: "Monday", 1: "Tuesday"}

    # Busy schedules (minutes relative to 09:00)
    bobby_busy = {
        0: [(330, 360)],  # Monday: 14:30-15:00
        1: [(0, 150), (180, 210), (240, 360), (390, 480)]  # Tuesday
    }

    michael_busy = {
        0: [(0, 60), (90, 270), (300, 360), (390, 480)],  # Monday
        1: [(0, 90), (120, 150), (180, 300), (360, 420), (450, 480)]  # Tuesday
    }

    # Z3 variables
    day = Int('day')      # 0 or 1
    start = Int('start')  # minutes from 09:00

    opt = Optimize()

    # Domain constraints
    opt.add(Or(day == 0, day == 1))
    opt.add(start >= 0, start + DURATION <= WORKDAY_MINUTES)

    # Availability constraints per participant and per day
    for d in [0, 1]:
        for (bs, be) in bobby_busy[d]:
            opt.add(Implies(day == d, no_overlap(start, DURATION, bs, be)))
        for (bs, be) in michael_busy[d]:
            opt.add(Implies(day == d, no_overlap(start, DURATION, bs, be)))

    # Earliest availability (minimize absolute minutes since Monday 09:00)
    absolute_start = day * WORKDAY_MINUTES + start
    opt.minimize(absolute_start)

    if opt.check().r == 1:  # sat
        m = opt.model()
        d_val = m.evaluate(day).as_long()
        s_val = m.evaluate(start).as_long()
        e_val = s_val + DURATION

        day_str = day_names[d_val]
        start_str = minutes_to_hhmm(s_val)
        end_str = minutes_to_hhmm(e_val)

        # Output includes both the time range and the day of the week
        print(f"{day_str} {{{start_str}:{end_str}}}")
    else:
        print("No feasible meeting time found.")

if __name__ == "__main__":
    main()