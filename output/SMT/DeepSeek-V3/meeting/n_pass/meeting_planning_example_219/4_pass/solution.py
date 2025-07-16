from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define all time points in minutes since midnight
    castro_arrival = 540  # 9:00 AM (540 minutes)
    
    # Friend availability windows
    emily_start_avail = 705   # 11:45 AM
    emily_end_avail = 915      # 3:15 PM
    barbara_start_avail = 1005 # 4:45 PM
    barbara_end_avail = 1095   # 6:15 PM
    william_start_avail = 1095 # 5:15 PM
    william_end_avail = 1200   # 7:00 PM

    # Meeting duration requirements
    emily_min_duration = 105  # 1 hour 45 minutes
    barbara_min_duration = 60 # 1 hour
    william_min_duration = 105 # 1 hour 45 minutes

    # Travel times in minutes
    castro_to_alamo = 8
    alamo_to_union = 14
    union_to_china = 7

    # Define meeting start and end times
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Add constraints for Emily
    s.add(emily_start >= emily_start_avail)
    s.add(emily_end <= emily_end_avail)
    s.add(emily_end - emily_start >= emily_min_duration)
    s.add(emily_start >= castro_arrival + castro_to_alamo)

    # Add constraints for Barbara
    s.add(barbara_start >= barbara_start_avail)
    s.add(barbara_end <= barbara_end_avail)
    s.add(barbara_end - barbara_start >= barbara_min_duration)
    s.add(barbara_start >= emily_end + alamo_to_union)

    # Add constraints for William
    s.add(william_start >= william_start_avail)
    s.add(william_end <= william_end_avail)
    s.add(william_end - william_start >= william_min_duration)
    s.add(william_start >= barbara_end + union_to_china)

    # Check for satisfiability
    if s.check() == sat:
        m = s.model()
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            hours = hours % 12
            if hours == 0:
                hours = 12
            return f"{hours}:{mins:02d} {ampm}"

        print("SOLUTION:")
        print(f"1. Meet Emily at Alamo Square from {format_time(m[emily_start].as_long())} to {format_time(m[emily_end].as_long())}")
        print(f"2. Travel to Union Square (14 mins)")
        print(f"3. Meet Barbara at Union Square from {format_time(m[barbara_start].as_long())} to {format_time(m[barbara_end].as_long())}")
        print(f"4. Travel to Chinatown (7 mins)")
        print(f"5. Meet William at Chinatown from {format_time(m[william_start].as_long())} to {format_time(m[william_end].as_long())}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()