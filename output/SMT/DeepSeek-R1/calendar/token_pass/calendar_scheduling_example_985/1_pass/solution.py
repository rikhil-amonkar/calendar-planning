from z3 import *

def main():
    # Define the variables
    day = Int('day')
    start = Int('start')  # Start time in minutes from midnight

    # Define the solver
    s = Solver()

    # Define the busy intervals for Diane and Matthew for each day (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday)
    # Each interval is (start_minute, end_minute) from midnight
    busy_diane = {
        0: [(720, 750), (900, 930)],  # Monday: 12:00-12:30, 15:00-15:30
        1: [(600, 660), (690, 720), (750, 780), (960, 1020)],  # Tuesday: 10:00-11:00, 11:30-12:00, 12:30-13:00, 16:00-17:00
        2: [(540, 570), (870, 900), (990, 1020)],  # Wednesday: 9:00-9:30, 14:30-15:00, 16:30-17:00
        3: [(930, 990)],  # Thursday: 15:30-16:30
        4: [(570, 690), (870, 900), (960, 1020)]  # Friday: 9:30-11:30, 14:30-15:00, 16:00-17:00
    }

    busy_matthew = {
        0: [(540, 600), (630, 1020)],  # Monday: 9:00-10:00, 10:30-17:00
        1: [(540, 1020)],  # Tuesday: 9:00-17:00
        2: [(540, 660), (720, 870), (960, 1020)],  # Wednesday: 9:00-11:00, 12:00-14:30, 16:00-17:00
        3: [(540, 960)],  # Thursday: 9:00-16:00
        4: [(540, 1020)]  # Friday: 9:00-17:00
    }

    # Constraints: day must be between 0 and 4 (Monday to Friday)
    s.add(day >= 0, day <= 4)
    # Meeting must be within work hours (9:00 to 17:00) and duration of 60 minutes
    s.add(start >= 540, start <= 960)  # 540=9:00, 960=16:00 (so that start+60 <= 1020=17:00)

    # Add constraints for each day
    for d in range(5):
        # For Diane's busy intervals on day d
        diane_constraints = []
        for interval in busy_diane[d]:
            s_busy, e_busy = interval
            # Meeting must not overlap: either ends before busy starts or starts after busy ends
            diane_constraints.append(Or(start + 60 <= s_busy, start >= e_busy))
        # For Matthew's busy intervals on day d
        matthew_constraints = []
        for interval in busy_matthew[d]:
            s_busy, e_busy = interval
            matthew_constraints.append(Or(start + 60 <= s_busy, start >= e_busy))
        
        # If day is d, then apply the constraints
        s.add(If(day == d, And(And(diane_constraints), And(matthew_constraints)), True))

    # Matthew's preference: not on Wednesday before 12:30 (750 minutes from midnight)
    s.add(If(day == 2, start >= 750, True))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start].as_long()
        end_val = start_val + 60

        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_time = minutes_to_time(start_val)
        end_time = minutes_to_time(end_val)

        # Map day index to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]

        # Output the result
        print(f"{day_name} {start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()