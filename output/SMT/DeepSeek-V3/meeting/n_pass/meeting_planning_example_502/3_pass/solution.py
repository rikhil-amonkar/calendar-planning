from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Convert all times to minutes from 9:00 AM (0 is 9:00 AM)
    # Joseph: Pacific Heights, 8:15 AM to 9:30 AM (not possible, as we arrive at 9:00 AM)
    # Since Joseph's window is before 9:00 AM, we cannot meet him.
    # Rebecca: Fisherman's Wharf, 8:00 AM to 11:15 AM
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    # Stephanie: Golden Gate Park, 11:00 AM to 3:00 PM
    stephanie_start = Int('stephanie_start')
    stephanie_end = Int('stephanie_end')
    # Karen: Chinatown, 1:45 PM to 4:30 PM
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')
    # Brian: Union Square, 3:00 PM to 5:15 PM
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')
    # Steven: North Beach, 2:30 PM to 8:45 PM
    steven_start = Int('steven_start')
    steven_end = Int('steven_end')

    # Convert all times to minutes since 9:00 AM (0 is 9:00 AM)
    # Rebecca's window: 8:00 AM to 11:15 AM is -60 to 135 minutes from 9:00 AM
    # But since we arrive at 9:00 AM, earliest we can meet Rebecca is 9:00 AM (0)
    # So Rebecca's window is 0 to 135 minutes (11:15 AM)
    s.add(rebecca_start >= 0)
    s.add(rebecca_end <= 135)
    s.add(rebecca_end - rebecca_start >= 30)  # min 30 minutes

    # Stephanie's window: 11:00 AM to 3:00 PM is 120 to 360 minutes
    s.add(stephanie_start >= 120)
    s.add(stephanie_end <= 360)
    s.add(stephanie_end - stephanie_start >= 105)  # min 105 minutes

    # Karen's window: 1:45 PM to 4:30 PM is 285 to 450 minutes
    s.add(karen_start >= 285)
    s.add(karen_end <= 450)
    s.add(karen_end - karen_start >= 15)  # min 15 minutes

    # Brian's window: 3:00 PM to 5:15 PM is 360 to 495 minutes
    s.add(brian_start >= 360)
    s.add(brian_end <= 495)
    s.add(brian_end - brian_start >= 30)  # min 30 minutes

    # Steven's window: 2:30 PM to 8:45 PM is 330 to 705 minutes
    s.add(steven_start >= 330)
    s.add(steven_end <= 705)
    s.add(steven_end - steven_start >= 120)  # min 120 minutes

    # Define the order of meetings and travel times
    # We start at Financial District at time 0 (9:00 AM)
    # Possible meetings: Rebecca, Stephanie, Karen, Brian, Steven
    # Let's assume the order is Rebecca -> Stephanie -> Karen -> Brian -> Steven
    # We need to model the sequence with travel times

    # Travel times:
    # Financial District to Fisherman's Wharf: 10 minutes
    # Fisherman's Wharf to Golden Gate Park: 25 minutes
    # Golden Gate Park to Chinatown: 23 minutes
    # Chinatown to Union Square: 7 minutes
    # Union Square to North Beach: 10 minutes

    # Constraints for the order:
    s.add(rebecca_start >= 10)  # travel from Financial District to Fisherman's Wharf (10 minutes)
    # After Rebecca, travel to Stephanie
    s.add(stephanie_start >= rebecca_end + 25)  # travel from Fisherman's Wharf to Golden Gate Park (25 minutes)
    # After Stephanie, travel to Karen
    s.add(karen_start >= stephanie_end + 23)  # travel from Golden Gate Park to Chinatown (23 minutes)
    # After Karen, travel to Brian
    s.add(brian_start >= karen_end + 7)  # travel from Chinatown to Union Square (7 minutes)
    # After Brian, travel to Steven
    s.add(steven_start >= brian_end + 10)  # travel from Union Square to North Beach (10 minutes)

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Convert minutes back to time format
        def minutes_to_time(minutes):
            hours = (minutes // 60) + 9  # Starting from 9:00 AM
            mins = minutes % 60
            am_pm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {am_pm}"
        
        print(f"Meet Rebecca at Fisherman's Wharf from {minutes_to_time(m[rebecca_start].as_long())} to {minutes_to_time(m[rebecca_end].as_long())}.")
        print(f"Meet Stephanie at Golden Gate Park from {minutes_to_time(m[stephanie_start].as_long())} to {minutes_to_time(m[stephanie_end].as_long())}.")
        print(f"Meet Karen at Chinatown from {minutes_to_time(m[karen_start].as_long())} to {minutes_to_time(m[karen_end].as_long())}.")
        print(f"Meet Brian at Union Square from {minutes_to_time(m[brian_start].as_long())} to {minutes_to_time(m[brian_end].as_long())}.")
        print(f"Meet Steven at North Beach from {minutes_to_time(m[steven_start].as_long())} to {minutes_to_time(m[steven_end].as_long())}.")
    else:
        print("No feasible schedule found.")

solve_scheduling()