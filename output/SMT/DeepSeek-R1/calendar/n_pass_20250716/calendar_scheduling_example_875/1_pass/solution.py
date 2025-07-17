import z3

def main():
    # Convert time string to minutes since midnight
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return hours * 60 + minutes

    # Predefined busy intervals for Natalie and William for each day
    natalie_busy = {
        0: [(time_str_to_minutes("9:00"), time_str_to_minutes("9:30")),
            (time_str_to_minutes("10:00"), time_str_to_minutes("12:00")),
            (time_str_to_minutes("12:30"), time_str_to_minutes("13:00")),
            (time_str_to_minutes("14:00"), time_str_to_minutes("14:30")),
            (time_str_to_minutes("15:00"), time_str_to_minutes("16:30"))],
        1: [(time_str_to_minutes("9:00"), time_str_to_minutes("9:30")),
            (time_str_to_minutes("10:00"), time_str_to_minutes("10:30")),
            (time_str_to_minutes("12:30"), time_str_to_minutes("14:00")),
            (time_str_to_minutes("16:00"), time_str_to_minutes("17:00"))],
        2: [(time_str_to_minutes("11:00"), time_str_to_minutes("11:30")),
            (time_str_to_minutes("16:00"), time_str_to_minutes("16:30"))],
        3: [(time_str_to_minutes("10:00"), time_str_to_minutes("11:00")),
            (time_str_to_minutes("11:30"), time_str_to_minutes("15:00")),
            (time_str_to_minutes("15:30"), time_str_to_minutes("16:00")),
            (time_str_to_minutes("16:30"), time_str_to_minutes("17:00"))]
    }

    william_busy = {
        0: [(time_str_to_minutes("9:30"), time_str_to_minutes("11:00")),
            (time_str_to_minutes("11:30"), time_str_to_minutes("17:00"))],
        1: [(time_str_to_minutes("9:00"), time_str_to_minutes("13:00")),
            (time_str_to_minutes("13:30"), time_str_to_minutes("16:00"))],
        2: [(time_str_to_minutes("9:00"), time_str_to_minutes("12:30")),
            (time_str_to_minutes("13:00"), time_str_to_minutes("14:30")),
            (time_str_to_minutes("15:30"), time_str_to_minutes("16:00")),
            (time_str_to_minutes("16:30"), time_str_to_minutes("17:00"))],
        3: [(time_str_to_minutes("9:00"), time_str_to_minutes("10:30")),
            (time_str_to_minutes("11:00"), time_str_to_minutes("11:30")),
            (time_str_to_minutes("12:00"), time_str_to_minutes("12:30")),
            (time_str_to_minutes("13:00"), time_str_to_minutes("14:00")),
            (time_str_to_minutes("15:00"), time_str_to_minutes("17:00"))]
    }

    # Z3 variables
    s = z3.Int('s')  # Start time in minutes
    d = z3.Int('d')  # Day: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday

    solver = z3.Solver()

    # Constraints for day and start time
    solver.add(d >= 0, d <= 3)
    solver.add(s >= time_str_to_minutes("9:00"))
    solver.add(s + 60 <= time_str_to_minutes("17:00"))  # Meeting ends by 17:00

    # Constraints for Natalie's busy intervals
    for day_index, intervals in natalie_busy.items():
        for start, end in intervals:
            solver.add(z3.Implies(d == day_index, z3.Or(s + 60 <= start, s >= end)))

    # Constraints for William's busy intervals
    for day_index, intervals in william_busy.items():
        for start, end in intervals:
            solver.add(z3.Implies(d == day_index, z3.Or(s + 60 <= start, s >= end)))

    # Check for a solution
    if solver.check() == z3.sat:
        model = solver.model()
        d_val = model[d].as_long()
        s_val = model[s].as_long()
        
        # Convert day index to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[d_val]
        
        # Format start and end times
        def minutes_to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        start_time_str = minutes_to_time_str(s_val)
        end_time_str = minutes_to_time_str(s_val + 60)
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()