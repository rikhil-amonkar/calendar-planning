import z3

def minutes_to_time(minutes):
    total_minutes_since_midnight = 9 * 60 + minutes
    hours = total_minutes_since_midnight // 60
    mins = total_minutes_since_midnight % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Busy intervals in minutes since 9:00 AM
    brian_busy = {
        0: [(30, 60), (210, 330), (390, 420)],  # Monday
        1: [(0, 30)],                            # Tuesday
        2: [(210, 240), (450, 480)],             # Wednesday
        3: [(120, 150), (240, 270), (450, 480)],  # Thursday
        4: [(30, 60), (90, 120), (240, 270), (360, 420), (450, 480)]  # Friday
    }

    julia_busy = {
        0: [(0, 60), (120, 150), (210, 240), (390, 420)],  # Monday
        1: [(240, 300), (420, 450)],                     # Tuesday
        2: [(0, 150), (180, 210), (240, 480)],           # Wednesday
        3: [(0, 90), (120, 480)],                        # Thursday
        4: [(0, 60), (90, 150), (210, 300), (300, 330), (390, 420)]  # Friday
    }

    solver = z3.Optimize()

    day = z3.Int('day')
    start_time = z3.Int('start_time')

    # Constraints on day and start_time
    solver.add(z3.And(day >= 0, day <= 4))
    solver.add(z3.And(start_time >= 0, start_time <= 420))

    # Add constraints for Brian's busy times
    for d in brian_busy:
        for (b_start, b_end) in brian_busy[d]:
            c = z3.Implies(day == d, z3.Or(start_time + 60 <= b_start, start_time >= b_end))
            solver.add(c)

    # Add constraints for Julia's busy times
    for d in julia_busy:
        for (b_start, b_end) in julia_busy[d]:
            c = z3.Implies(day == d, z3.Or(start_time + 60 <= b_start, start_time >= b_end))
            solver.add(c)

    # Objective function to minimize
    penalty = z3.If(day == 0, 10000, 0)
    objective = penalty + day * 1000 + start_time
    solver.minimize(objective)

    if solver.check() == z3.sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = start_val + 60

        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]

        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()