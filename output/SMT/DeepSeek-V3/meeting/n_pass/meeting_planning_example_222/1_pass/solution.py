from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Helen at North Beach
    helen_start = Int('helen_start')  # in minutes since 9:00 AM (540)
    helen_end = Int('helen_end')
    
    # Kimberly at Fisherman's Wharf
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    
    # Patricia at Bayview
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')
    
    # Define travel times (in minutes)
    # From Nob Hill to North Beach: 8
    # From North Beach to Fisherman's Wharf: 5
    # From Fisherman's Wharf to Bayview: 26
    
    # Constraints for Helen (North Beach: 7:00 AM - 4:45 PM, min 120 minutes)
    # Convert times to minutes since 9:00 AM (540 minutes since midnight)
    # Helen's availability: 7:00 AM (420) to 4:45 PM (16*60 + 45 = 1005)
    # Since our time starts at 9:00 AM (540), subtract 540 to get relative times
    helen_min_start = 420 - 540  # 7:00 AM is -120 (relative to 9:00 AM)
    helen_max_end = 1005 - 540    # 4:45 PM is 465 (relative to 9:00 AM)
    
    s.add(helen_start >= helen_min_start)
    s.add(helen_end <= helen_max_end)
    s.add(helen_end - helen_start >= 120)  # min 120 minutes
    
    # Constraints for Kimberly (Fisherman's Wharf: 4:30 PM - 9:00 PM, min 45 minutes)
    # 4:30 PM is 16*60 + 30 = 990; 9:00 PM is 21*60 = 1260
    kimberly_min_start = 990 - 540  # 450
    kimberly_max_end = 1260 - 540   # 720
    s.add(kimberly_start >= kimberly_min_start)
    s.add(kimberly_end <= kimberly_max_end)
    s.add(kimberly_end - kimberly_start >= 45)
    
    # Constraints for Patricia (Bayview: 6:00 PM - 9:15 PM, min 120 minutes)
    # 6:00 PM is 18*60 = 1080; 9:15 PM is 21*60 + 15 = 1275
    patricia_min_start = 1080 - 540  # 540
    patricia_max_end = 1275 - 540    # 735
    s.add(patricia_start >= patricia_min_start)
    s.add(patricia_end <= patricia_max_end)
    s.add(patricia_end - patricia_start >= 120)
    
    # Travel constraints
    # Start at Nob Hill at time 0 (9:00 AM)
    # First travel to North Beach (Helen): takes 8 minutes
    s.add(helen_start >= 8)  # can't meet Helen before arriving at North Beach
    
    # Travel from North Beach to Fisherman's Wharf (Kimberly): takes 5 minutes
    s.add(kimberly_start >= helen_end + 5)
    
    # Travel from Fisherman's Wharf to Bayview (Patricia): takes 26 minutes
    s.add(patricia_start >= kimberly_end + 26)
    
    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        # Convert times back to absolute minutes since midnight
        base_time = 540  # 9:00 AM in minutes since midnight
        helen_s = m.eval(helen_start).as_long() + base_time
        helen_e = m.eval(helen_end).as_long() + base_time
        kimberly_s = m.eval(kimberly_start).as_long() + base_time
        kimberly_e = m.eval(kimberly_end).as_long() + base_time
        patricia_s = m.eval(patricia_start).as_long() + base_time
        patricia_e = m.eval(patricia_end).as_long() + base_time
        
        # Print the schedule
        print("SOLUTION:")
        print(f"Meet Helen at North Beach from {minutes_to_time(helen_s)} to {minutes_to_time(helen_e)}")
        print(f"Meet Kimberly at Fisherman's Wharf from {minutes_to_time(kimberly_s)} to {minutes_to_time(kimberly_e)}")
        print(f"Meet Patricia at Bayview from {minutes_to_time(patricia_s)} to {minutes_to_time(patricia_e)}")
    else:
        print("No feasible schedule found.")

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solve_scheduling()