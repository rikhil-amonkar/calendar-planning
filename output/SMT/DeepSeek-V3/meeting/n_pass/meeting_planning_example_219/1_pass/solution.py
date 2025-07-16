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
    # Travel from The Castro to Alamo Square (for Emily)
    travel_to_emily_start = Int('travel_to_emily_start')
    travel_to_emily_end = Int('travel_to_emily_end')
    # Travel from Alamo Square to Union Square (for Barbara)
    travel_to_barbara_start = Int('travel_to_barbara_start')
    travel_to_barbara_end = Int('travel_to_barbara_end')
    # Travel from Union Square to Chinatown (for William)
    travel_to_william_start = Int('travel_to_william_start')
    travel_to_william_end = Int('travel_to_william_end')

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
    s.add(travel_to_emily_start >= castro_arrival_time)
    s.add(travel_to_emily_end == travel_to_emily_start + 8)
    s.add(emily_start >= travel_to_emily_end)

    # Travel from Alamo Square to Union Square takes 14 minutes
    s.add(travel_to_barbara_start >= emily_end)
    s.add(travel_to_barbara_end == travel_to_barbara_start + 14)
    s.add(barbara_start >= travel_to_barbara_end)

    # Travel from Union Square to Chinatown takes 7 minutes
    s.add(travel_to_william_start >= barbara_end)
    s.add(travel_to_william_end == travel_to_william_start + 7)
    s.add(william_start >= travel_to_william_end)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Emily from {m[emily_start].as_long() // 60}:{m[emily_start].as_long() % 60:02d} to {m[emily_end].as_long() // 60}:{m[emily_end].as_long() % 60:02d}")
        print(f"Meet Barbara from {m[barbara_start].as_long() // 60}:{m[barbara_start].as_long() % 60:02d} to {m[barbara_end].as_long() // 60}:{m[barbara_end].as_long() % 60:02d}")
        print(f"Meet William from {m[william_start].as_long() // 60}:{m[william_start].as_long() % 60:02d} to {m[william_end].as_long() // 60}:{m[william_end].as_long() % 60:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()