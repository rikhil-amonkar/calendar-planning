from z3 import *

def main():
    day = Int('day')
    start = Int('start')
    s = Solver()

    s.add(day >= 0, day <= 4)
    s.add(start >= 0, start <= 450)

    eugene_busy = {
        0: [(120, 180), (270, 300), (330, 360), (420, 450)],
        1: [],
        2: [(0, 30), (120, 150), (180, 210), (270, 360)],
        3: [(30, 60), (120, 210)],
        4: [(90, 120), (180, 210), (240, 270)]
    }

    eric_busy = {
        0: [(0, 480)],
        1: [(0, 480)],
        2: [(0, 150), (180, 300), (330, 450)],
        3: [(0, 480)],
        4: [(0, 120), (150, 480)]
    }

    for d in range(5):
        for interval in eugene_busy[d]:
            b_start, b_end = interval
            s.add(If(day == d, Or(start + 30 <= b_start, start >= b_end), True))
        for interval in eric_busy[d]:
            b_start, b_end = interval
            s.add(If(day == d, Or(start + 30 <= b_start, start >= b_end), True))

    s1 = Solver()
    s1.add(s.assertions())
    s1.add(day != 2)

    if s1.check() == sat:
        m = s1.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
    else:
        s2 = Solver()
        s2.add(s.assertions())
        if s2.check() == sat:
            m = s2.model()
            d_val = m[day].as_long()
            start_val = m[start].as_long()
        else:
            print("No solution found")
            return

    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[d_val]
    total_minutes = start_val
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    end_minutes = start_val + 30
    end_hours = 9 + end_minutes // 60
    end_minutes %= 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"

    print(f"Day: {day_str}, Start: {start_time}, End: {end_time}")

if __name__ == '__main__':
    main()