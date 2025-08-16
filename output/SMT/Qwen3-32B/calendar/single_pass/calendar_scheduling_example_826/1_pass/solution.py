from z3 import *

def to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Define James's schedule per day (in minutes since midnight)
    schedule = [
        # Monday
        [(540, 570), (630, 660), (750, 780), (870, 930), (990, 1020)],
        # Tuesday
        [(540, 660), (690, 720), (750, 930), (960, 1020)],
        # Wednesday
        [(600, 660), (720, 780), (810, 960)],
        # Thursday
        [(570, 690), (720, 750), (780, 810), (840, 870), (990, 1020)]
    ]

    opt = Optimize()

    day = Int('day')
    start_time = Int('start_time')

    # Constraints for day and time range
    opt.add(And(day >= 0, day <= 3))
    opt.add(And(start_time >= 540, start_time <= 990))  # 9:00 to 16:30

    # Add constraints for each meeting on each day
    for day_idx in range(4):
        for (s, e) in schedule[day_idx]:
            # If the current day is day_idx, then the start_time must not overlap with this meeting
            opt.add(Implies(day == day_idx, Or(start_time + 30 <= s, start_time >= e)))

    # Minimize day first, then start_time
    opt.minimize(day)
    opt.minimize(start_time)

    if opt.check() == sat:
        m = opt.model()
        d = m.eval(day).as_long()
        st = m.eval(start_time).as_long()
        et = st + 30

        days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
        day_name = days[d]

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {to_time(st)}")
        print(f"End Time: {to_time(et)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()