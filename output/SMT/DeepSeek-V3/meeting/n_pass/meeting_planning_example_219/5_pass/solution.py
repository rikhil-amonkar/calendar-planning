from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Time points in minutes since midnight
    current_time = 540  # 9:00 AM (540 minutes)

    # Friend availability windows
    emily_available = (705, 915)    # 11:45 AM - 3:15 PM
    barbara_available = (1005, 1095) # 4:45 PM - 6:15 PM
    william_available = (1095, 1200)  # 5:15 PM - 7:00 PM

    # Minimum meeting durations
    emily_min_duration = 105
    barbara_min_duration = 60
    william_min_duration = 105

    # Travel times between locations
    travel_times = {
        ('Castro', 'Alamo'): 8,
        ('Alamo', 'Union'): 14,
        ('Union', 'Chinatown'): 7
    }

    # Define meeting variables
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Emily constraints
    s.add(emily_start >= emily_available[0])
    s.add(emily_end <= emily_available[1])
    s.add(emily_end - emily_start >= emily_min_duration)
    s.add(emily_start >= current_time + travel_times[('Castro', 'Alamo')])

    # Barbara constraints
    s.add(barbara_start >= barbara_available[0])
    s.add(barbara_end <= barbara_available[1])
    s.add(barbara_end - barbara_start >= barbara_min_duration)
    s.add(barbara_start >= emily_end + travel_times[('Alamo', 'Union')])

    # William constraints
    s.add(william_start >= william_available[0])
    s.add(william_end <= william_available[1])
    s.add(william_end - william_start >= william_min_duration)
    s.add(william_start >= barbara_end + travel_times[('Union', 'Chinatown')])

    # Check solution
    if s.check() == sat:
        m = s.model()
        
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            period = "AM" if h < 12 else "PM"
            h = h % 12
            if h == 0: h = 12
            return f"{h}:{m:02d} {period}"

        print("SOLUTION:")
        print(f"9:00 AM - Arrive at The Castro")
        print(f"Travel to Alamo Square (8 mins)")
        print(f"Meet Emily from {format_time(m[emily_start].as_long())} to {format_time(m[emily_end].as_long())}")
        print(f"Travel to Union Square (14 mins)")
        print(f"Meet Barbara from {format_time(m[barbara_start].as_long())} to {format_time(m[barbara_end].as_long())}")
        print(f"Travel to Chinatown (7 mins)")
        print(f"Meet William from {format_time(m[william_start].as_long())} to {format_time(m[william_end].as_long())}")
    else:
        print("No valid schedule found that meets all constraints.")

solve_scheduling()