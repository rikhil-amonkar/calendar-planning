from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables (using Real for more precision)
    timothy_start = Real('timothy_start')
    timothy_end = Real('timothy_end')
    david_start = Real('david_start')
    david_end = Real('david_end')
    robert_start = Real('robert_start')
    robert_end = Real('robert_end')

    # Travel times (minutes)
    fd_to_ph = 13
    ph_to_fw = 13
    fw_to_md = 22

    # Available time windows (converted to minutes since midnight)
    timothy_available_start = 9 * 60    # 9:00 AM
    timothy_available_end = 15 * 60 + 30  # 3:30 PM
    david_available_start = 10 * 60 + 45  # 10:45 AM
    david_available_end = 15 * 60 + 30    # 3:30 PM
    robert_available_start = 12 * 60 + 15  # 12:15 PM
    robert_available_end = 19 * 60 + 45    # 7:45 PM

    # Meeting duration requirements
    timothy_duration = 75
    david_duration = 15
    robert_duration = 90

    # Constraints for Timothy
    s.add(timothy_start >= timothy_available_start)
    s.add(timothy_end <= timothy_available_end)
    s.add(timothy_end - timothy_start >= timothy_duration)

    # Constraints for David
    s.add(david_start >= david_available_start)
    s.add(david_end <= david_available_end)
    s.add(david_end - david_start >= david_duration)

    # Constraints for Robert
    s.add(robert_start >= robert_available_start)
    s.add(robert_end <= robert_available_end)
    s.add(robert_end - robert_start >= robert_duration)

    # Travel sequence constraints
    arrival_at_ph = 9 * 60 + fd_to_ph  # Arrival at Pacific Heights
    s.add(timothy_start >= arrival_at_ph)
    
    departure_from_ph = timothy_end
    arrival_at_fw = departure_from_ph + ph_to_fw
    s.add(david_start >= arrival_at_fw)
    
    departure_from_fw = david_end
    arrival_at_md = departure_from_fw + fw_to_md
    s.add(robert_start >= arrival_at_md)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def format_time(minutes):
            h = int(m[minutes].as_fraction().numerator_as_long() / 
                   m[minutes].as_fraction().denominator_as_long() / 60)
            mnt = int(m[minutes].as_fraction().numerator_as_long() / 
                     m[minutes].as_fraction().denominator_as_long() % 60)
            return f"{h}:{mnt:02d}"
        
        print(f"1. Meet Timothy at Pacific Heights from {format_time(timothy_start)} to {format_time(timothy_end)}")
        print(f"2. Meet David at Fisherman's Wharf from {format_time(david_start)} to {format_time(david_end)}")
        print(f"3. Meet Robert at Mission District from {format_time(robert_start)} to {format_time(robert_end)}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()