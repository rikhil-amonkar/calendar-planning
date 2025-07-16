from z3 import *

def solve_schedule():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    ronald_start = Int('ronald_start')
    ronald_end = Int('ronald_end')
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')
    joshua_start = Int('joshua_start')
    joshua_end = Int('joshua_end')
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Convert time windows to minutes since 9:00 AM
    ronald_window = (60, 480)    # 10:00 AM - 5:00 PM
    helen_window = (270, 480)    # 1:30 PM - 5:00 PM
    joshua_window = (315, 630)   # 2:15 PM - 7:30 PM
    margaret_window = (75, 780)  # 10:15 AM - 10:00 PM

    # Minimum meeting durations
    min_ronald = 105
    min_helen = 120
    min_joshua = 90
    min_margaret = 60

    # Travel times (in minutes)
    pac_haight = 11   # Pacific Heights to Haight-Ashbury
    haight_nob = 15   # Haight-Ashbury to Nob Hill
    nob_castro = 17   # Nob Hill to The Castro
    castro_sunset = 17 # The Castro to Sunset District

    # Add constraints for each meeting
    # Ronald
    s.add(ronald_start >= ronald_window[0])
    s.add(ronald_end <= ronald_window[1])
    s.add(ronald_end - ronald_start >= min_ronald)

    # Helen
    s.add(helen_start >= helen_window[0])
    s.add(helen_end <= helen_window[1])
    s.add(helen_end - helen_start >= min_helen)

    # Joshua
    s.add(joshua_start >= joshua_window[0])
    s.add(joshua_end <= joshua_window[1])
    s.add(joshua_end - joshua_start >= min_joshua)

    # Margaret
    s.add(margaret_start >= margaret_window[0])
    s.add(margaret_end <= margaret_window[1])
    s.add(margaret_end - margaret_start >= min_margaret)

    # Define meeting sequence with travel times
    # Start at Pacific Heights at time 0
    # First meeting: Margaret at Haight-Ashbury
    s.add(margaret_start >= pac_haight)

    # From Margaret to Ronald
    s.add(ronald_start >= margaret_end + haight_nob)

    # From Ronald to Helen
    s.add(helen_start >= ronald_end + nob_castro)

    # From Helen to Joshua
    s.add(joshua_start >= helen_end + castro_sunset)

    # Check if schedule is feasible
    if s.check() == sat:
        m = s.model()
        
        def format_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            hours = hours if hours <= 12 else hours - 12
            return f"{hours}:{mins:02d} {ampm}"

        print("\nOptimal Schedule:")
        print("-----------------")
        print(f"1. Meet Margaret at Haight-Ashbury:")
        print(f"   Start: {format_time(m[margaret_start].as_long())}")
        print(f"   End:   {format_time(m[margaret_end].as_long())}")
        print(f"   Duration: {min_margaret} minutes")
        
        print(f"\n2. Travel to Nob Hill (15 minutes)")
        
        print(f"\n3. Meet Ronald at Nob Hill:")
        print(f"   Start: {format_time(m[ronald_start].as_long())}")
        print(f"   End:   {format_time(m[ronald_end].as_long())}")
        print(f"   Duration: {min_ronald} minutes")
        
        print(f"\n4. Travel to The Castro (17 minutes)")
        
        print(f"\n5. Meet Helen at The Castro:")
        print(f"   Start: {format_time(m[helen_start].as_long())}")
        print(f"   End:   {format_time(m[helen_end].as_long())}")
        print(f"   Duration: {min_helen} minutes")
        
        print(f"\n6. Travel to Sunset District (17 minutes)")
        
        print(f"\n7. Meet Joshua at Sunset District:")
        print(f"   Start: {format_time(m[joshua_start].as_long())}")
        print(f"   End:   {format_time(m[joshua_end].as_long())}")
        print(f"   Duration: {min_joshua} minutes")
        
        print("\nTotal meetings scheduled: 4")
    else:
        print("\nNo feasible schedule found that meets all constraints.")

solve_schedule()