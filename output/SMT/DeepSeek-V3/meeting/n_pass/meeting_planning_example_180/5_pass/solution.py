from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    arrival_time = 540  # 9:00 AM
    james_start_min = 765  # 12:45 PM
    james_end_max = 840   # 2:00 PM
    robert_start_min = 765  # 12:45 PM
    robert_end_max = 915   # 3:15 PM

    # Travel times in minutes
    nb_to_md = 18
    nb_to_castro = 22
    md_to_castro = 7
    castro_to_md = 7

    # Meeting duration requirements
    min_james_duration = 75
    min_robert_duration = 30

    # Variables for meeting times
    james_start = Int('james_start')
    james_end = Int('james_end')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Basic meeting constraints
    s.add(james_start >= james_start_min)
    s.add(james_end <= james_end_max)
    s.add(james_end - james_start >= min_james_duration)
    
    s.add(robert_start >= robert_start_min)
    s.add(robert_end <= robert_end_max)
    s.add(robert_end - robert_start >= min_robert_duration)

    # Option 1: Meet James first, then Robert
    option1 = And(
        james_start >= arrival_time + nb_to_md,
        robert_start >= james_end + md_to_castro
    )

    # Option 2: Meet Robert first, then James
    option2 = And(
        robert_start >= arrival_time + nb_to_castro,
        james_start >= robert_end + castro_to_md
    )

    s.add(Or(option1, option2))

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

        if rs >= je + md_to_castro:
            print("SOLUTION: Meet James first, then Robert")
            print(f"1. Depart North Beach at {format_time(arrival_time)}")
            print(f"2. Arrive Mission District at {format_time(arrival_time + nb_to_md)}")
            print(f"3. Meet James: {format_time(js)} to {format_time(je)}")
            print(f"4. Travel to The Castro (arrive {format_time(je + md_to_castro)})")
            print(f"5. Meet Robert: {format_time(rs)} to {format_time(re)}")
        else:
            print("SOLUTION: Meet Robert first, then James")
            print(f"1. Depart North Beach at {format_time(arrival_time)}")
            print(f"2. Arrive The Castro at {format_time(arrival_time + nb_to_castro)}")
            print(f"3. Meet Robert: {format_time(rs)} to {format_time(re)}")
            print(f"4. Travel to Mission District (arrive {format_time(re + castro_to_md)})")
            print(f"5. Meet James: {format_time(js)} to {format_time(je)}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()