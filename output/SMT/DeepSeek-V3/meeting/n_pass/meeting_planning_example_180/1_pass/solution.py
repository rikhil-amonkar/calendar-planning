from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # James availability: 12:45 PM (765 minutes) to 2:00 PM (840 minutes)
    # Robert availability: 12:45 PM (765 minutes) to 3:15 PM (915 minutes)
    # Travel times in minutes
    nb_to_md = 18
    nb_to_castro = 22
    md_to_nb = 17
    md_to_castro = 7
    castro_to_nb = 20
    castro_to_md = 7

    # Variables for meeting start and end times
    # Meeting with James at Mission District
    james_start = Int('james_start')
    james_end = Int('james_end')
    # Meeting with Robert at The Castro
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Constraints for James
    s.add(james_start >= 765)  # 12:45 PM
    s.add(james_end <= 840)    # 2:00 PM
    s.add(james_end - james_start >= 75)

    # Constraints for Robert
    s.add(robert_start >= 765)  # 12:45 PM
    s.add(robert_end <= 915)    # 3:15 PM
    s.add(robert_end - robert_start >= 30)

    # Arrival at North Beach at 9:00 AM (540 minutes)
    # We need to decide the order of meetings: James first or Robert first

    # Option 1: Meet James first, then Robert
    # Travel from North Beach to Mission District (18 minutes), then to The Castro (7 minutes)
    option1 = And(
        james_start >= 540 + nb_to_md,  # Travel to Mission District
        robert_start >= james_end + md_to_castro  # Travel to The Castro after meeting James
    )

    # Option 2: Meet Robert first, then James
    # Travel from North Beach to The Castro (22 minutes), then to Mission District (7 minutes)
    option2 = And(
        robert_start >= 540 + nb_to_castro,  # Travel to The Castro
        james_start >= robert_end + castro_to_md  # Travel to Mission District after meeting Robert
    )

    # Add either option1 or option2 to the solver
    s.add(Or(option1, option2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Convert times back to hours and minutes
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # Since 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours}:{mins:02d}"

        # Extract values
        js = m.evaluate(james_start).as_long()
        je = m.evaluate(james_end).as_long()
        rs = m.evaluate(robert_start).as_long()
        re = m.evaluate(robert_end).as_long()

        # Determine order
        if rs >= je + md_to_castro:
            order = "North Beach -> Mission District (meet James) -> The Castro (meet Robert)"
        else:
            order = "North Beach -> The Castro (meet Robert) -> Mission District (meet James)"

        print("SOLUTION:")
        print(f"Order of meetings: {order}")
        print(f"Meet James from {minutes_to_time(js - 540)} to {minutes_to_time(je - 540)}")
        print(f"Meet Robert from {minutes_to_time(rs - 540)} to {minutes_to_time(re - 540)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()