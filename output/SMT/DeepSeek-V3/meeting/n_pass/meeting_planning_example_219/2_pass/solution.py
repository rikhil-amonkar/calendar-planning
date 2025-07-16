from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Define variables for travel times
    travel_to_emily = Int('travel_to_emily')  # Time to travel to Alamo Square (Emily)
    travel_to_barbara = Int('travel_to_barbara')  # Time to travel to Union Square (Barbara)
    travel_to_william = Int('travel_to_william')  # Time to travel to Chinatown (William)

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    castro_arrival_time = 540  # 9:00 AM in minutes

    # Emily's availability: 11:45 AM (705) to 3:15 PM (915)
    emily_available_start = 705
    emily_available_end = 915
    # Barbara's availability: 4:45 PM (1005) to 6:15 PM (1095)
    barbara_available_start = 1005
    barbara_available_end = 1095
    # William's availability: 5:15 PM (1095) to 7:00 PM (1200)
    william_available_start = 1095
    william_available_end = 1200

    # Constraints for Emily
    s.add(emily_start >= emily_available_start)
    s.add(emily_end <= emily_available_end)
    s.add(emily_end - emily_start >= 105)  # Minimum 105 minutes with Emily

    # Constraints for Barbara
    s.add(barbara_start >= barbara_available_start)
    s.add(barbara_end <= barbara_available_end)
    s.add(barbara_end - barbara_start >= 60)  # Minimum 60 minutes with Barbara

    # Constraints for William
    s.add(william_start >= william_available_start)
    s.add(william_end <= william_available_end)
    s.add(william_end - william_start >= 105)  # Minimum 105 minutes with William

    # Travel constraints
    # Travel from The Castro to Alamo Square takes 8 minutes
    s.add(travel_to_emily == 8)
    s.add(emily_start >= castro_arrival_time + travel_to_emily)

    # Travel from Alamo Square to Union Square takes 14 minutes
    s.add(travel_to_barbara == 14)
    s.add(barbara_start >= emily_end + travel_to_barbara)

    # Travel from Union Square to Chinatown takes 7 minutes
    s.add(travel_to_william == 7)
    s.add(william_start >= barbara_end + travel_to_william)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"

        print(f"Meet Emily from {minutes_to_time(m[emily_start].as_long())} to {minutes_to_time(m[emily_end].as_long())}")
        print(f"Meet Barbara from {minutes_to_time(m[barbara_start].as_long())} to {minutes_to_time(m[barbara_end].as_long())}")
        print(f"Meet William from {minutes_to_time(m[william_start].as_long())} to {minutes_to_time(m[william_end].as_long())}")
    else:
        print("No feasible schedule found.")

solve_scheduling()