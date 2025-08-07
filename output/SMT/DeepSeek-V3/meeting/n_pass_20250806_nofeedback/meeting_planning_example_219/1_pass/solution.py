from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Emily at Alamo Square
    emily_start = Int('emily_start')  # in minutes since 9:00 AM
    emily_end = Int('emily_end')
    
    # Meeting with Barbara at Union Square
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    
    # Meeting with William at Chinatown
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Convert friend's available times to minutes since 9:00 AM
    # Emily: 11:45 AM to 3:15 PM (11*60 + 45 = 705, 15*60 + 15 = 915)
    emily_available_start = 705 - 540  # 9:00 AM is 540 minutes (9*60)
    emily_available_end = 915 - 540
    
    # Barbara: 4:45 PM to 6:15 PM (16*60 + 45 = 1005, 18*60 + 15 = 1095)
    barbara_available_start = 1005 - 540
    barbara_available_end = 1095 - 540
    
    # William: 5:15 PM to 7:00 PM (17*60 + 15 = 1035, 19*60 = 1140)
    william_available_start = 1035 - 540
    william_available_end = 1140 - 540

    # Add constraints for meeting durations
    s.add(emily_end - emily_start >= 105)  # 105 minutes with Emily
    s.add(barbara_end - barbara_start >= 60)  # 60 minutes with Barbara
    s.add(william_end - william_start >= 105)  # 105 minutes with William

    # Add constraints for meeting within available times
    s.add(emily_start >= emily_available_start)
    s.add(emily_end <= emily_available_end)
    s.add(barbara_start >= barbara_available_start)
    s.add(barbara_end <= barbara_available_end)
    s.add(william_start >= william_available_start)
    s.add(william_end <= william_available_end)

    # Travel times (in minutes)
    # From The Castro to Alamo Square: 8
    # After meeting Emily, possible next locations:
    # From Alamo Square to Union Square: 14
    # From Alamo Square to Chinatown: 16
    # From Union Square to Chinatown: 7
    # From Chinatown to Union Square: 7

    # Assume the order is: Emily -> Barbara -> William
    # So travel from Alamo Square to Union Square after Emily: 14 minutes
    s.add(barbara_start >= emily_end + 14)
    # Then travel from Union Square to Chinatown: 7 minutes
    s.add(william_start >= barbara_end + 7)

    # Alternatively, could try other orders, but this seems plausible.

    # Also, initial travel from The Castro to Alamo Square: 8 minutes
    s.add(emily_start >= 8)  # since starting at 9:00 AM (0 minutes), travel takes 8 minutes.

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        base_time = 9 * 60  # 9:00 AM in minutes

        emily_start_time = base_time + m[emily_start].as_long()
        emily_end_time = base_time + m[emily_end].as_long()
        barbara_start_time = base_time + m[barbara_start].as_long()
        barbara_end_time = base_time + m[barbara_end].as_long()
        william_start_time = base_time + m[william_start].as_long()
        william_end_time = base_time + m[william_end].as_long()

        # Format times as HH:MM
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": format_time(emily_start_time), "end_time": format_time(emily_end_time)},
            {"action": "meet", "person": "Barbara", "start_time": format_time(barbara_start_time), "end_time": format_time(barbara_end_time)},
            {"action": "meet", "person": "William", "start_time": format_time(william_start_time), "end_time": format_time(william_end_time)}
        ]

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))