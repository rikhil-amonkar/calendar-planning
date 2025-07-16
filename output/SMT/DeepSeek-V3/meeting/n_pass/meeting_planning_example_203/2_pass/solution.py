from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since midnight)
    # Meeting with Timothy at Pacific Heights
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')

    # Meeting with David at Fisherman's Wharf
    david_start = Int('david_start')
    david_end = Int('david_end')

    # Meeting with Robert at Mission District
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Travel times (in minutes)
    travel_fd_to_ph = 13  # Financial District to Pacific Heights
    travel_ph_to_fw = 13  # Pacific Heights to Fisherman's Wharf
    travel_fw_to_md = 22  # Fisherman's Wharf to Mission District

    # Constraints for Timothy (Pacific Heights)
    s.add(timothy_start >= 9 * 60)  # 9:00 AM
    s.add(timothy_end <= 15 * 60 + 30)  # 3:30 PM
    s.add(timothy_end - timothy_start >= 75)  # 75 minutes meeting

    # Constraints for David (Fisherman's Wharf)
    s.add(david_start >= 10 * 60 + 45)  # 10:45 AM
    s.add(david_end <= 15 * 60 + 30)    # 3:30 PM
    s.add(david_end - david_start >= 15)  # 15 minutes meeting

    # Constraints for Robert (Mission District)
    s.add(robert_start >= 12 * 60 + 15)  # 12:15 PM
    s.add(robert_end <= 19 * 60 + 45)    # 7:45 PM
    s.add(robert_end - robert_start >= 90)  # 90 minutes meeting

    # Arrival at Financial District at 9:00 AM (time = 9*60 = 540 minutes)

    # Assume the schedule is: Financial -> Pacific Heights -> Fisherman's Wharf -> Mission District
    # So the sequence is: 
    # 1. Travel to Pacific Heights (13 minutes), meet Timothy
    # 2. Travel to Fisherman's Wharf (13 minutes), meet David
    # 3. Travel to Mission District (22 minutes), meet Robert

    # Add travel and meeting sequence constraints
    s.add(timothy_start >= 9 * 60 + travel_fd_to_ph)  # arrive at Pacific Heights at 9:00 + 13 minutes travel
    s.add(david_start >= timothy_end + travel_ph_to_fw)  # travel from Pacific Heights to Fisherman's Wharf
    s.add(robert_start >= david_end + travel_fw_to_md)  # travel from Fisherman's Wharf to Mission District

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            return f"{minutes // 60}:{minutes % 60:02d}"
        print(f"Meet Timothy at Pacific Heights from {minutes_to_time(m[timothy_start].as_long())} to {minutes_to_time(m[timothy_end].as_long())}")
        print(f"Meet David at Fisherman's Wharf from {minutes_to_time(m[david_start].as_long())} to {minutes_to_time(m[david_end].as_long())}")
        print(f"Meet Robert at Mission District from {minutes_to_time(m[robert_start].as_long())} to {minutes_to_time(m[robert_end].as_long())}")
    else:
        print("No feasible schedule found.")

solve_scheduling()