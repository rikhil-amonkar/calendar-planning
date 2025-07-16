from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define all times in minutes since 9:00 AM (540 minutes since midnight)
    base_time = 540

    # Define variables for meeting durations and start times
    helen_duration = Int('helen_duration')
    kimberly_duration = Int('kimberly_duration')
    patricia_duration = Int('patricia_duration')

    helen_start = Int('helen_start')  # Minutes since base_time
    kimberly_start = Int('kimberly_start')
    patricia_start = Int('patricia_start')

    # Minimum meeting durations
    min_helen = 120
    min_kimberly = 45
    min_patricia = 120

    # Travel times (minutes)
    to_north_beach = 8
    to_fishermans_wharf = 5
    to_bayview = 26

    # Friend availability windows (relative to base_time)
    helen_min = -120  # 7:00 AM (420) - 540 = -120
    helen_max = 465    # 4:45 PM (1005) - 540 = 465
    kimberly_min = 450 # 4:30 PM (990) - 540 = 450
    kimberly_max = 720 # 9:00 PM (1260) - 540 = 720
    patricia_min = 540 # 6:00 PM (1080) - 540 = 540
    patricia_max = 735 # 9:15 PM (1275) - 540 = 735

    # Meeting duration constraints
    s.add(helen_duration >= min_helen)
    s.add(kimberly_duration >= min_kimberly)
    s.add(patricia_duration >= min_patricia)

    # Meeting window constraints
    s.add(helen_start >= helen_min)
    s.add(helen_start + helen_duration <= helen_max)
    s.add(kimberly_start >= kimberly_min)
    s.add(kimberly_start + kimberly_duration <= kimberly_max)
    s.add(patricia_start >= patricia_min)
    s.add(patricia_start + patricia_duration <= patricia_max)

    # Travel sequence constraints
    s.add(helen_start >= to_north_beach)  # Can't meet Helen before arriving
    s.add(kimberly_start >= helen_start + helen_duration + to_fishermans_wharf)
    s.add(patricia_start >= kimberly_start + kimberly_duration + to_bayview)

    # Check for feasible schedule
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Helen at North Beach from {format_time(base_time + m[helen_start].as_long())} to {format_time(base_time + m[helen_start].as_long() + m[helen_duration].as_long())}")
        print(f"Meet Kimberly at Fisherman's Wharf from {format_time(base_time + m[kimberly_start].as_long())} to {format_time(base_time + m[kimberly_start].as_long() + m[kimberly_duration].as_long())}")
        print(f"Meet Patricia at Bayview from {format_time(base_time + m[patricia_start].as_long())} to {format_time(base_time + m[patricia_start].as_long() + m[patricia_duration].as_long())}")
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