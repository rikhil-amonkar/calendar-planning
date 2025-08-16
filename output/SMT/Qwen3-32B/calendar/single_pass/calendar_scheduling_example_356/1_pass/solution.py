from z3 import Solver, Int, Or, sat

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    s = Solver()

    # Define the start time in minutes since midnight
    S = Int('S')

    # Work hours: 9:00 AM (540) to 5:00 PM (1020), meeting is 30 minutes long
    s.add(S >= 540)
    s.add(S <= 990)

    # Katherine's busy intervals (12:00-12:30, 13:00-14:30)
    katherine_buses = [(720, 750), (780, 870)]
    for a, b in katherine_buses:
        s.add(Or(S + 30 <= a, S >= b))

    # Julie's busy intervals (9:00-9:30, 10:30-11:00, 13:30-14:00, 15:00-15:30)
    julie_buses = [(540, 570), (630, 660), (810, 840), (900, 930)]
    for a, b in julie_buses:
        s.add(Or(S + 30 <= a, S >= b))

    # Angela's busy intervals (9:00-10:00, 10:30-11:00, 11:30-14:00, 14:30-15:00, 16:30-17:00)
    angela_buses = [(540, 600), (630, 660), (690, 840), (870, 900), (990, 1020)]
    for a, b in angela_buses:
        s.add(Or(S + 30 <= a, S >= b))

    # Nicholas's blocked times (9:30-11:00, 11:30-13:30, 14:00-16:00, 16:30-17:00)
    nicholas_buses = [(570, 660), (690, 810), (840, 960), (990, 1020)]
    for a, b in nicholas_buses:
        s.add(Or(S + 30 <= a, S >= b))

    # Carl's blocked times (9:00-11:00, 11:30-12:30, 13:00-14:30, 15:00-16:00, 16:30-17:00)
    carl_buses = [(540, 660), (690, 750), (780, 870), (900, 960), (990, 1020)]
    for a, b in carl_buses:
        s.add(Or(S + 30 <= a, S >= b))

    # Solve and print the result
    if s.check() == sat:
        m = s.model()
        S_val = m.evaluate(S).as_long()
        start_time = S_val
        end_time = S_val + 30

        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {to_time_str(start_time)}")
        print(f"End Time: {to_time_str(end_time)}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()