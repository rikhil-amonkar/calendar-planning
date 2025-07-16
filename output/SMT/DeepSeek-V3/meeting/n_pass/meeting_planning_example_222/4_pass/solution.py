from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since midnight)
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')

    # Define travel times (in minutes)
    travel = {
        ('Nob Hill', 'North Beach'): 8,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('Fisherman\'s Wharf', 'Bayview'): 26
    }

    # Constraints for Helen (North Beach: 7:00 AM - 4:45 PM, min 120 minutes)
    s.add(helen_start >= 7*60)       # 7:00 AM
    s.add(helen_end <= 16*60 + 45)   # 4:45 PM
    s.add(helen_end - helen_start >= 120)

    # Constraints for Kimberly (Fisherman's Wharf: 4:30 PM - 9:00 PM, min 45 minutes)
    s.add(kimberly_start >= 16*60 + 30)  # 4:30 PM
    s.add(kimberly_end <= 21*60)         # 9:00 PM
    s.add(kimberly_end - kimberly_start >= 45)

    # Constraints for Patricia (Bayview: 6:00 PM - 9:15 PM, min 120 minutes)
    s.add(patricia_start >= 18*60)       # 6:00 PM
    s.add(patricia_end <= 21*60 + 15)    # 9:15 PM
    s.add(patricia_end - patricia_start >= 120)

    # Starting at Nob Hill at 9:00 AM (540 minutes)
    start_time = 9*60

    # Sequence of meetings with travel times
    # 1. Travel to North Beach (8 minutes)
    s.add(helen_start >= start_time + travel[('Nob Hill', 'North Beach')])
    
    # 2. Travel to Fisherman's Wharf (5 minutes after meeting Helen)
    s.add(kimberly_start >= helen_end + travel[('North Beach', 'Fisherman\'s Wharf')])
    
    # 3. Travel to Bayview (26 minutes after meeting Kimberly)
    s.add(patricia_start >= kimberly_end + travel[('Fisherman\'s Wharf', 'Bayview')])

    # Check for feasible schedule
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Helen at North Beach from {format_time(m[helen_start].as_long())} to {format_time(m[helen_end].as_long())}")
        print(f"Meet Kimberly at Fisherman's Wharf from {format_time(m[kimberly_start].as_long())} to {format_time(m[kimberly_end].as_long())}")
        print(f"Meet Patricia at Bayview from {format_time(m[patricia_start].as_long())} to {format_time(m[patricia_end].as_long())}")
    else:
        print("No feasible schedule found.")

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    ampm = "AM" if hours < 12 else "PM"
    hours = hours % 12
    if hours == 0:
        hours = 12
    return f"{hours}:{mins:02d} {ampm}"

solve_scheduling()