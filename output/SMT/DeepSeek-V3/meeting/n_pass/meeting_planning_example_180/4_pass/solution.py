from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight for easier calculations
    # Arrival at North Beach at 9:00 AM (540 minutes)
    # James availability: 12:45 PM (765 minutes) to 2:00 PM (840 minutes)
    # Robert availability: 12:45 PM (765 minutes) to 3:15 PM (915 minutes)
    # Travel times in minutes
    nb_to_md = 18
    nb_to_castro = 22
    md_to_castro = 7
    castro_to_md = 7

    # Variables for meeting start and end times
    james_start = Int('james_start')
    james_end = Int('james_end')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Constraints for James
    s.add(james_start >= 765)  # 12:45 PM
    s.add(james_end <= 840)    # 2:00 PM
    s.add(james_end - james_start >= 75)  # At least 75 minutes

    # Constraints for Robert
    s.add(robert_start >= 765)  # 12:45 PM
    s.add(robert_end <= 915)    # 3:15 PM
    s.add(robert_end - robert_start >= 30)  # At least 30 minutes

    # Option 1: Meet James first, then Robert
    option1 = And(
        james_start >= 540 + nb_to_md,  # Travel to Mission District
        robert_start >= james_end + md_to_castro  # Travel to The Castro
    )

    # Option 2: Meet Robert first, then James
    option2 = And(
        robert_start >= 540 + nb_to_castro,  # Travel to The Castro
        james_start >= robert_end + castro_to_md  # Travel to Mission District
    )

    # Add either option to the solver
    s.add(Or(option1, option2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            elif hours == 0:
                hours = 12
            return f"{hours}:{mins:02d} {ampm}"

        js = m.evaluate(james_start).as_long()
        je = m.evaluate(james_end).as_long()
        rs = m.evaluate(robert_start).as_long()
        re = m.evaluate(robert_end).as_long()

        # Determine order
        if rs >= je + md_to_castro:
            order = "North Beach → Mission District → The Castro"
            print("SOLUTION:")
            print(f"1. Leave North Beach at {format_time(540)}")
            print(f"2. Arrive at Mission District at {format_time(540 + nb_to_md)}")
            print(f"3. Meet James from {format_time(js)} to {format_time(je)}")
            print(f"4. Travel to The Castro (takes {md_to_castro} minutes)")
            print(f"5. Meet Robert from {format_time(rs)} to {format_time(re)}")
        else:
            order = "North Beach → The Castro → Mission District"
            print("SOLUTION:")
            print(f"1. Leave North Beach at {format_time(540)}")
            print(f"2. Arrive at The Castro at {format_time(540 + nb_to_castro)}")
            print(f"3. Meet Robert from {format_time(rs)} to {format_time(re)}")
            print(f"4. Travel to Mission District (takes {castro_to_md} minutes)")
            print(f"5. Meet James from {format_time(js)} to {format_time(je)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()