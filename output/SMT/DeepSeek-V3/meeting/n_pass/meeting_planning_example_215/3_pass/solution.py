from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations
    BAYVIEW, EMBARCADERO, RICHMOND, FISHERMAN = 0, 1, 2, 3
    loc_names = ["Bayview", "Embarcadero", "Richmond District", "Fisherman's Wharf"]

    # Travel times matrix (minutes)
    travel = [
        [0, 19, 25, 25],  # From Bayview
        [21, 0, 21, 6],    # From Embarcadero
        [26, 19, 0, 18],   # From Richmond
        [26, 8, 18, 0]     # From Fisherman's Wharf
    ]

    # Convert all times to minutes since 9:00 AM
    def convert_time(h, m):
        return (h - 9) * 60 + m

    # Meeting availability windows
    jason_start = convert_time(16, 0)    # 4:00 PM
    jason_end = convert_time(16, 45)     # 4:45 PM
    jessica_start = convert_time(16, 45) # 4:45 PM
    jessica_end = convert_time(19, 0)    # 7:00 PM
    sandra_start = convert_time(18, 30)  # 6:30 PM
    sandra_end = convert_time(21, 45)    # 9:45 PM

    # Minimum meeting durations
    jason_min = 30
    jessica_min = 30
    sandra_min = 120

    # Meeting time variables
    jason_meet_start = Int('jason_start')
    jason_meet_end = Int('jason_end')
    jessica_meet_start = Int('jessica_start')
    jessica_meet_end = Int('jessica_end')
    sandra_meet_start = Int('sandra_start')
    sandra_meet_end = Int('sandra_end')

    # Meeting location sequence
    loc_after_jason = Int('loc_after_jason')
    loc_after_jessica = Int('loc_after_jessica')

    # Base constraints for each meeting
    s.add(jason_meet_start >= jason_start)
    s.add(jason_meet_end <= jason_end)
    s.add(jason_meet_end - jason_meet_start >= jason_min)
    
    s.add(jessica_meet_start >= jessica_start)
    s.add(jessica_meet_end <= jessica_end)
    s.add(jessica_meet_end - jessica_meet_start >= jessica_min)
    
    s.add(sandra_meet_start >= sandra_start)
    s.add(sandra_meet_end <= sandra_end)
    s.add(sandra_meet_end - sandra_meet_start >= sandra_min)

    # Starting location is Bayview
    s.add(jason_meet_start >= travel[BAYVIEW][FISHERMAN])

    # Sequence constraints
    s.add(loc_after_jason == FISHERMAN)
    s.add(jessica_meet_start >= jason_meet_end + travel[FISHERMAN][EMBARCADERO])
    
    s.add(loc_after_jessica == EMBARCADERO)
    s.add(sandra_meet_start >= jessica_meet_end + travel[EMBARCADERO][RICHMOND])

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"1. Meet Jason at Fisherman's Wharf:")
        print(f"   Start: {m[jason_meet_start].as_long()} mins after 9:00 AM")
        print(f"   End:   {m[jason_meet_end].as_long()} mins after 9:00 AM")
        
        print(f"\n2. Meet Jessica at Embarcadero:")
        print(f"   Start: {m[jessica_meet_start].as_long()} mins after 9:00 AM")
        print(f"   End:   {m[jessica_meet_end].as_long()} mins after 9:00 AM")
        
        print(f"\n3. Meet Sandra at Richmond District:")
        print(f"   Start: {m[sandra_meet_start].as_long()} mins after 9:00 AM")
        print(f"   End:   {m[sandra_meet_end].as_long()} mins after 9:00 AM")
        
        # Calculate total time used
        total_time = m[sandra_meet_end].as_long()
        print(f"\nTotal time from 9:00 AM: {total_time} minutes")
    else:
        print("No valid schedule found that meets all constraints")

solve_scheduling()