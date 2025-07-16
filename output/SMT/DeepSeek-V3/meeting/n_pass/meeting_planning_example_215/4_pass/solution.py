from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Location indices
    BAYVIEW, EMBARCADERO, RICHMOND, FISHERMAN = 0, 1, 2, 3
    loc_names = ["Bayview", "Embarcadero", "Richmond District", "Fisherman's Wharf"]

    # Travel time matrix (minutes)
    travel_time = [
        [0, 19, 25, 25],  # Bayview to others
        [21, 0, 21, 6],    # Embarcadero to others
        [26, 19, 0, 18],   # Richmond to others
        [26, 8, 18, 0]     # Fisherman's Wharf to others
    ]

    # Convert clock time to minutes since 9:00 AM
    def to_minutes(h, m):
        return (h - 9) * 60 + m

    # Meeting availability windows
    jason_window = (to_minutes(16, 0), to_minutes(16, 45))    # 4:00-4:45 PM
    jessica_window = (to_minutes(16, 45), to_minutes(19, 0)) # 4:45-7:00 PM
    sandra_window = (to_minutes(18, 30), to_minutes(21, 45))  # 6:30-9:45 PM

    # Minimum meeting durations
    jason_duration = 30
    jessica_duration = 30
    sandra_duration = 120

    # Meeting time variables
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    jessica_start = Int('jessica_start')
    jessica_end = Int('jessica_end')
    sandra_start = Int('sandra_start')
    sandra_end = Int('sandra_end')

    # Meeting location sequence variables
    after_jason = Int('after_jason')
    after_jessica = Int('after_jessica')

    # Base meeting constraints
    # Jason at Fisherman's Wharf
    s.add(jason_start >= jason_window[0])
    s.add(jason_end <= jason_window[1])
    s.add(jason_end - jason_start >= jason_duration)
    
    # Jessica at Embarcadero
    s.add(jessica_start >= jessica_window[0])
    s.add(jessica_end <= jessica_window[1])
    s.add(jessica_end - jessica_start >= jessica_duration)
    
    # Sandra at Richmond District
    s.add(sandra_start >= sandra_window[0])
    s.add(sandra_end <= sandra_window[1])
    s.add(sandra_end - sandra_start >= sandra_duration)

    # Starting from Bayview at 9:00 AM (time = 0)
    # First meeting: Jason at Fisherman's Wharf
    s.add(jason_start >= travel_time[BAYVIEW][FISHERMAN])
    s.add(after_jason == FISHERMAN)

    # Second meeting: Jessica at Embarcadero
    s.add(jessica_start >= jason_end + travel_time[FISHERMAN][EMBARCADERO])
    s.add(after_jessica == EMBARCADERO)

    # Third meeting: Sandra at Richmond District
    s.add(sandra_start >= jessica_end + travel_time[EMBARCADERO][RICHMOND])

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        # Function to format time
        def format_time(minutes):
            h = 9 + minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d} {'AM' if h < 12 else 'PM'}"

        print(f"1. Meet Jason at Fisherman's Wharf:")
        print(f"   Start: {format_time(m[jason_start].as_long())}")
        print(f"   End:   {format_time(m[jason_end].as_long())}")
        
        print(f"\n2. Meet Jessica at Embarcadero:")
        print(f"   Start: {format_time(m[jessica_start].as_long())}")
        print(f"   End:   {format_time(m[jessica_end].as_long())}")
        
        print(f"\n3. Meet Sandra at Richmond District:")
        print(f"   Start: {format_time(m[sandra_start].as_long())}")
        print(f"   End:   {format_time(m[sandra_end].as_long())}")
        
        # Calculate total time used
        total_minutes = m[sandra_end].as_long()
        print(f"\nTotal time from 9:00 AM: {total_minutes} minutes "
              f"({total_minutes//60}h {total_minutes%60}m)")
    else:
        print("No valid schedule found that meets all constraints")

solve_scheduling()