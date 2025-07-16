from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables (in minutes since 9:00 AM)
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Travel times (minutes)
    PH_to_Presidio = 11
    PH_to_Marina = 6
    Presidio_to_Marina = 10
    Marina_to_Presidio = 10

    # Time windows (minutes since 9:00 AM)
    # Jason: 10:00 AM (60) to 4:15 PM (435)
    # Kenneth: 3:30 PM (390) to 4:45 PM (465)

    # Meeting duration constraints
    s.add(jason_end - jason_start >= 90)  # At least 90 minutes with Jason
    s.add(kenneth_end - kenneth_start >= 45)  # At least 45 minutes with Kenneth

    # Time window constraints
    s.add(jason_start >= 60, jason_end <= 435)
    s.add(kenneth_start >= 390, kenneth_end <= 465)

    # Travel constraints - consider both possible orders
    # Option 1: PH -> Presidio (Jason) -> Marina (Kenneth)
    option1 = And(
        jason_start >= PH_to_Presidio,
        kenneth_start >= jason_end + Presidio_to_Marina
    )

    # Option 2: PH -> Marina (Kenneth) -> Presidio (Jason)
    option2 = And(
        kenneth_start >= PH_to_Marina,
        jason_start >= kenneth_end + Marina_to_Presidio
    )

    s.add(Or(option1, option2))

    if s.check() == sat:
        m = s.model()
        js = m.eval(jason_start).as_long()
        je = m.eval(jason_end).as_long()
        ks = m.eval(kenneth_start).as_long()
        ke = m.eval(kenneth_end).as_long()

        def format_time(minutes):
            total = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total // 60
            mins = total % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {ampm}"

        print("SOLUTION:")
        print(f"Meet Jason at Presidio from {format_time(js)} to {format_time(je)}")
        print(f"Meet Kenneth at Marina District from {format_time(ks)} to {format_time(ke)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()