from z3 import Solver, Int, If, Or, And, sat

def main():
    day = Int('day')
    start = Int('start')

    base_constraints = [
        day >= 0,
        day <= 1,
        start >= 0,
        start <= 450,  # 450 minutes ensures the meeting ends by 17:00
        # Jean's constraints: only on Tuesday
        If(day == 1,
           And(
               Or(start + 30 <= 150, start >= 180),  # Avoid 11:30-12:00
               Or(start + 30 <= 420, start >= 450)     # Avoid 16:00-16:30
           ),
           True  # No constraints on Monday
        ),
        # Doris's constraints
        If(day == 0,
           Or(
               And(start >= 150, start + 30 <= 180),  # 11:30-12:00
               And(start >= 210, start + 30 <= 270),  # 12:30-13:30
               And(start >= 420, start + 30 <= 450)   # 16:00-16:30
           ),
           False  # No availability on Tuesday
        )
    ]

    # First try with Doris's preference: meeting ends by 14:00 (300 minutes)
    s1 = Solver()
    s1.add(base_constraints)
    s1.add(start + 30 <= 300)

    if s1.check() == sat:
        m = s1.model()
    else:
        # Without the preference constraint
        s2 = Solver()
        s2.add(base_constraints)
        if s2.check() == sat:
            m = s2.model()
        else:
            print("No solution found")
            return

    d_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = start_val + 30

    # Convert minutes to time strings
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_hour = 9 + end_val // 60
    end_minute = end_val % 60

    days = ["Monday", "Tuesday"]
    day_str = days[d_val]
    start_time = f"{start_hour}:{start_minute:02d}"
    end_time = f"{end_hour}:{end_minute:02d}"

    print(f"Day: {day_str}, Start: {start_time}, End: {end_time}")

if __name__ == "__main__":
    main()