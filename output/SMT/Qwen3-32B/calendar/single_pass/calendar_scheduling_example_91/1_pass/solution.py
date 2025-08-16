import z3

def main():
    # Define all intervals for existing meetings
    danielle_meetings = [
        (9*60, 10*60),                   # 9:00-10:00
        (10*60 + 30, 11*60),            # 10:30-11:00
        (14*60 + 30, 15*60),            # 14:30-15:00
        (15*60 + 30, 16*60),            # 15:30-16:00
        (16*60 + 30, 17*60)             # 16:30-17:00
    ]
    bruce_meetings = [
        (11*60, 11*60 + 30),           # 11:00-11:30
        (12*60 + 30, 13*60),           # 12:30-13:00
        (14*60, 14*60 + 30),           # 14:00-14:30
        (15*60 + 30, 16*60)            # 15:30-16:00
    ]
    eric_meetings = [
        (9*60, 9*60 + 30),            # 9:00-9:30
        (10*60, 11*60),               # 10:00-11:00
        (11*60 + 30, 13*60),          # 11:30-13:00
        (14*60 + 30, 15*60 + 30)      # 14:30-15:30
    ]
    all_intervals = danielle_meetings + bruce_meetings + eric_meetings

    # Create Z3 solver and variable for the meeting start time
    solver = z3.Solver()
    S = z3.Int('S')

    # Add constraints for valid work hours (9:00 to 17:00) and one-hour meeting
    solver.add(S >= 9*60)
    solver.add(S <= 17*60 - 60)  # S + 60 <= 17:00 (1020)

    # Add constraints for no overlap with existing meetings
    for start, end in all_intervals:
        solver.add(z3.Or(S + 60 <= start, end <= S))

    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        S_val = model[S].as_long()
        start_time = S_val
        end_time = S_val + 60

        # Format time in 24-hour format
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        day = "Monday"
        start_str = format_time(start_time)
        end_str = format_time(end_time)

        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()