from z3 import *

def main():
    # Define the start variable
    start = Int('start')
    solver = Solver()

    # Add the constraint that start is between 9:00 (540) and 16:30 (990)
    solver.add(And(start >= 540, start <= 990))

    # Define blocked intervals for each participant in minutes
    diane_blocked = [(9*60 + 30, 9*60 + 60), (14*60 + 30, 14*60 + 60)]  # 570-600, 870-900
    jack_blocked = [(13*60 + 30, 13*60 + 60), (14*60 + 30, 14*60 + 60)]  # 810-840, 870-900
    eugene_blocked = [(9*60, 10*60), (10*60 + 30, 11*60 + 30), (12*60, 14*60 + 30), (15*60, 16*60 + 30)]
    patricia_blocked = [(9*60 + 30, 10*60 + 30), (11*60, 12*60), (12*60 + 30, 14*60), (15*60, 16*60 + 30)]

    all_blocked = [
        diane_blocked,
        jack_blocked,
        eugene_blocked,
        patricia_blocked
    ]

    # For each blocked interval in all participants, add constraints
    for blocked in all_blocked:
        for (s, e) in blocked:
            solver.add(Or(start + 30 <= s, start >= e))

    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_val = model[start].as_long()
        end_val = start_val + 30

        # Convert to time strings
        def to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        start_time_str = to_time_str(start_val)
        end_time_str = to_time_str(end_val)

        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()