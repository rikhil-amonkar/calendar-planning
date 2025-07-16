from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables (using integers for minutes since midnight)
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    david_start = Int('david_start')
    david_end = Int('david_end')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Travel times in minutes
    fd_to_ph = 13  # Financial District to Pacific Heights
    ph_to_fw = 13  # Pacific Heights to Fisherman's Wharf
    fw_to_md = 22  # Fisherman's Wharf to Mission District

    # Time windows in minutes since midnight
    timothy_window_start = 9 * 60      # 9:00 AM
    timothy_window_end = 15 * 60 + 30  # 3:30 PM
    david_window_start = 10 * 60 + 45  # 10:45 AM
    david_window_end = 15 * 60 + 30    # 3:30 PM
    robert_window_start = 12 * 60 + 15  # 12:15 PM
    robert_window_end = 19 * 60 + 45    # 7:45 PM

    # Meeting duration requirements
    timothy_min_duration = 75  # minutes
    david_min_duration = 15    # minutes
    robert_min_duration = 90   # minutes

    # Meeting duration constraints
    s.add(timothy_end - timothy_start >= timothy_min_duration)
    s.add(david_end - david_start >= david_min_duration)
    s.add(robert_end - robert_start >= robert_min_duration)

    # Time window constraints
    s.add(timothy_start >= timothy_window_start)
    s.add(timothy_end <= timothy_window_end)
    s.add(david_start >= david_window_start)
    s.add(david_end <= david_window_end)
    s.add(robert_start >= robert_window_start)
    s.add(robert_end <= robert_window_end)

    # Travel sequence constraints
    # Start at Financial District at 9:00 AM
    arrival_at_ph = 9 * 60 + fd_to_ph  # Arrival at Pacific Heights
    s.add(timothy_start >= arrival_at_ph)
    
    # Travel from Pacific Heights to Fisherman's Wharf
    departure_from_ph = timothy_end
    arrival_at_fw = departure_from_ph + ph_to_fw
    s.add(david_start >= arrival_at_fw)
    
    # Travel from Fisherman's Wharf to Mission District
    departure_from_fw = david_end
    arrival_at_md = departure_from_fw + fw_to_md
    s.add(robert_start >= arrival_at_md)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        # Get the actual values from the model
        ts = m[timothy_start].as_long()
        te = m[timothy_end].as_long()
        ds = m[david_start].as_long()
        de = m[david_end].as_long()
        rs = m[robert_start].as_long()
        re = m[robert_end].as_long()
        
        print(f"1. Meet Timothy at Pacific Heights from {format_time(ts)} to {format_time(te)}")
        print(f"2. Meet David at Fisherman's Wharf from {format_time(ds)} to {format_time(de)}")
        print(f"3. Meet Robert at Mission District from {format_time(rs)} to {format_time(re)}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()