from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Joseph is not possible since his window is before 9:00 AM
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

    # Time constraints for each meeting
    s.add(rebecca_start >= 0)  # Earliest possible at 9:00 AM (0 minutes)
    s.add(rebecca_end <= 135)  # 11:15 AM is 135 minutes after 9:00 AM
    s.add(rebecca_end - rebecca_start >= 30)  # Min 30 minutes

    s.add(stephanie_start >= 120)  # 11:00 AM is 120 minutes after 9:00 AM
    s.add(stephanie_end <= 360)    # 3:00 PM is 360 minutes after 9:00 AM
    s.add(stephanie_end - stephanie_start >= 105)  # Min 105 minutes

    s.add(karen_start >= 285)  # 1:45 PM is 285 minutes after 9:00 AM
    s.add(karen_end <= 450)    # 4:30 PM is 450 minutes after 9:00 AM
    s.add(karen_end - karen_start >= 15)  # Min 15 minutes

    s.add(brian_start >= 360)  # 3:00 PM is 360 minutes after 9:00 AM
    s.add(brian_end <= 495)    # 5:15 PM is 495 minutes after 9:00 AM
    s.add(brian_end - brian_start >= 30)  # Min 30 minutes

    s.add(steven_start >= 330)  # 2:30 PM is 330 minutes after 9:00 AM
    s.add(steven_end <= 705)    # 8:45 PM is 705 minutes after 9:00 AM
    s.add(steven_end - steven_start >= 120)  # Min 120 minutes

    # Travel time constraints
    # Starting at Financial District at 9:00 AM (time = 0)
    s.add(rebecca_start >= 10)  # Travel to Fisherman's Wharf takes 10 minutes

    # From Fisherman's Wharf to Golden Gate Park takes 25 minutes
    s.add(stephanie_start >= rebecca_end + 25)

    # From Golden Gate Park to Chinatown takes 23 minutes
    s.add(karen_start >= stephanie_end + 23)

    # From Chinatown to Union Square takes 7 minutes
    s.add(brian_start >= karen_end + 7)

    # From Union Square to North Beach takes 10 minutes
    s.add(steven_start >= brian_end + 10)

    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def format_time(minutes):
            total_hours = 9 + (minutes // 60)
            mins = minutes % 60
            period = "AM" if total_hours < 12 else "PM"
            hour = total_hours if total_hours <= 12 else total_hours - 12
            return f"{hour}:{mins:02d} {period}"
        
        print(f"Meet Rebecca at Fisherman's Wharf from {format_time(m[rebecca_start].as_long())} to {format_time(m[rebecca_end].as_long())}")
        print(f"Meet Stephanie at Golden Gate Park from {format_time(m[stephanie_start].as_long())} to {format_time(m[stephanie_end].as_long())}")
        print(f"Meet Karen at Chinatown from {format_time(m[karen_start].as_long())} to {format_time(m[karen_end].as_long())}")
        print(f"Meet Brian at Union Square from {format_time(m[brian_start].as_long())} to {format_time(m[brian_end].as_long())}")
        print(f"Meet Steven at North Beach from {format_time(m[steven_start].as_long())} to {format_time(m[steven_end].as_long())}")
    else:
        print("No feasible schedule found.")

solve_scheduling()