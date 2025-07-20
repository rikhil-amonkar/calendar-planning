from z3 import *

def main():
    s = Solver()
    start = Int('start')

    # Meeting must be within 9:00 to 17:00 (0 to 480 minutes from 9:00)
    s.add(start >= 0)
    s.add(start + 30 <= 480)  # Meeting ends by 17:00

    # Adam's busy: 14:00-15:00 -> [300, 360)
    s.add(Or(start + 30 <= 300, start >= 360))

    # John's busy intervals: 
    # 13:00-13:30 [240, 270), 14:00-14:30 [300, 330), 15:30-16:00 [390, 420), 16:30-17:00 [450, 480)
    s.add(Or(start + 30 <= 240, start >= 270))
    s.add(Or(start + 30 <= 300, start >= 330))
    s.add(Or(start + 30 <= 390, start >= 420))
    s.add(Or(start + 30 <= 450, start >= 480))

    # Stephanie's busy intervals:
    # 9:30-10:00 [30,60), 10:30-11:00 [90,120), 11:30-16:00 [150,420), 16:30-17:00 [450,480)
    s.add(Or(start + 30 <= 30, start >= 60))
    s.add(Or(start + 30 <= 90, start >= 120))
    s.add(Or(start + 30 <= 150, start >= 420))
    s.add(Or(start + 30 <= 450, start >= 480))

    # Anna's busy intervals:
    # 9:30-10:00 [30,60), 12:00-12:30 [180,210), 13:00-15:30 [240,390), 16:30-17:00 [450,480)
    s.add(Or(start + 30 <= 30, start >= 60))
    s.add(Or(start + 30 <= 180, start >= 210))
    s.add(Or(start + 30 <= 240, start >= 390))
    s.add(Or(start + 30 <= 450, start >= 480))

    # Anna's preference: not before 14:30 (330 minutes)
    s.push()
    s.add(start >= 330)

    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
    else:
        s.pop()
        if s.check() == sat:
            m = s.model()
            start_val = m[start].as_long()
        else:
            print("No solution found")
            return

    total_minutes = start_val
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_hour = 9 + hours
    start_min = minutes
    start_str = f"{start_hour}:{start_min:02d}"

    end_minutes = total_minutes + 30
    end_hours = 9 + end_minutes // 60
    end_minutes_remainder = end_minutes % 60
    end_str = f"{end_hours}:{end_minutes_remainder:02d}"

    print(f"Monday {start_str} to {end_str}")

if __name__ == '__main__':
    main()