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
    nob_hill_to_north_beach = 8
    north_beach_to_fishermans_wharf = 5
    fishermans_wharf_to_bayview = 26

    # Constraints for Helen (North Beach: 7:00 AM - 4:45 PM, min 120 minutes)
    helen_min_start = 7 * 60  # 7:00 AM in minutes since midnight
    helen_max_end = 16 * 60 + 45  # 4:45 PM in minutes since midnight
    s.add(helen_start >= helen_min_start)
    s.add(helen_end <= helen_max_end)
    s.add(helen_end - helen_start >= 120)

    # Constraints for Kimberly (Fisherman's Wharf: 4:30 PM - 9:00 PM, min 45 minutes)
    kimberly_min_start = 16 * 60 + 30  # 4:30 PM in minutes since midnight
    kimberly_max_end = 21 * 60  # 9:00 PM in minutes since midnight
    s.add(kimberly_start >= kimberly_min_start)
    s.add(kimberly_end <= kimberly_max_end)
    s.add(kimberly_end - kimberly_start >= 45)

    # Constraints for Patricia (Bayview: 6:00 PM - 9:15 PM, min 120 minutes)
    patricia_min_start = 18 * 60  # 6:00 PM in minutes since midnight
    patricia_max_end = 21 * 60 + 15  # 9:15 PM in minutes since midnight
    s.add(patricia_start >= patricia_min_start)
    s.add(patricia_end <= patricia_max_end)
    s.add(patricia_end - patricia_start >= 120)

    # Starting at Nob Hill at 9:00 AM (540 minutes since midnight)
    start_time = 9 * 60  # 9:00 AM in minutes since midnight

    # Travel from Nob Hill to North Beach to meet Helen
    s.add(helen_start >= start_time + nob_hill_to_north_beach)

    # Travel from North Beach to Fisherman's Wharf to meet Kimberly
    s.add(kimberly_start >= helen_end + north_beach_to_fishermans_wharf)

    # Travel from Fisherman's Wharf to Bayview to meet Patricia
    s.add(patricia_start >= kimberly_end + fishermans_wharf_to_bayview)

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Helen at North Beach from {minutes_to_time(m[helen_start].as_long())} to {minutes_to_time(m[helen_end].as_long())}")
        print(f"Meet Kimberly at Fisherman's Wharf from {minutes_to_time(m[kimberly_start].as_long())} to {minutes_to_time(m[kimberly_end].as_long())}")
        print(f"Meet Patricia at Bayview from {minutes_to_time(m[patricia_start].as_long())} to {minutes_to_time(m[patricia_end].as_long())}")
    else:
        print("No feasible schedule found.")

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solve_scheduling()