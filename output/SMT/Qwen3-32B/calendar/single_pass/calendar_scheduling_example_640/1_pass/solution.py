import z3

def main():
    day = z3.Int('day')
    s = z3.Int('s')
    solver = z3.Optimize()

    # Day can be 0 (Monday) or 1 (Tuesday)
    solver.add(z3.Or(day == 0, day == 1))
    # s is between 0 and 450 inclusive
    solver.add(z3.And(s >= 0, s <= 450))

    # Bobby's busy intervals
    # Monday: [(330, 360)]
    for b_start, b_end in [(330, 360)]:
        solver.add(z3.Implies(day == 0, z3.Or(s + 30 <= b_start, s >= b_end)))
    # Tuesday: [(0, 150), (180, 210), (240, 360), (390, 480)]
    for b_start, b_end in [(0, 150), (180, 210), (240, 360), (390, 480)]:
        solver.add(z3.Implies(day == 1, z3.Or(s + 30 <= b_start, s >= b_end)))

    # Michael's busy intervals
    # Monday: [(0, 60), (90, 270), (300, 360), (390, 480)]
    for m_start, m_end in [(0, 60), (90, 270), (300, 360), (390, 480)]:
        solver.add(z3.Implies(day == 0, z3.Or(s + 30 <= m_start, s >= m_end)))
    # Tuesday: [(0, 90), (120, 150), (180, 300), (360, 420), (450, 480)]
    for m_start, m_end in [(0, 90), (120, 150), (180, 300), (360, 420), (450, 480)]:
        solver.add(z3.Implies(day == 1, z3.Or(s + 30 <= m_start, s >= m_end)))

    # Add objectives to minimize day, then s
    solver.minimize(day)
    solver.minimize(s)

    if solver.check() == z3.sat:
        model = solver.model()
        day_val = model.eval(day).as_long()
        s_val = model.eval(s).as_long()

        # Convert to day name
        day_name = 'Monday' if day_val == 0 else 'Tuesday'

        # Convert s_val to start and end times
        def format_time(minutes_since_9am):
            total_minutes = minutes_since_9am
            hours = 9 + total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_time_str = format_time(s_val)
        end_time_str = format_time(s_val + 30)

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()