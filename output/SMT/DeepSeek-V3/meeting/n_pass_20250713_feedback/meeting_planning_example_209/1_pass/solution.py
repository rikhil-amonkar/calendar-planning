from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Melissa at North Beach
    melissa_start = Real('melissa_start')
    melissa_end = Real('melissa_end')
    # Anthony at Chinatown
    anthony_start = Real('anthony_start')
    anthony_end = Real('anthony_end')
    # Rebecca at Russian Hill
    rebecca_start = Real('rebecca_start')
    rebecca_end = Real('rebecca_end')

    # Define travel times (in minutes)
    sunset_to_north_beach = 29
    north_beach_to_chinatown = 6
    chinatown_to_russian_hill = 7

    # Arrival time at Sunset District is 9:00 AM (540 minutes since midnight)
    arrival_time = 540  # 9:00 AM in minutes

    # Friends' availability windows
    # Melissa: 8:15 AM (495) to 1:30 PM (810)
    melissa_available_start = 495
    melissa_available_end = 810
    # Anthony: 1:15 PM (795) to 2:30 PM (870)
    anthony_available_start = 795
    anthony_available_end = 870
    # Rebecca: 7:30 PM (1170) to 9:15 PM (1215)
    rebecca_available_start = 1170
    rebecca_available_end = 1215

    # Minimum meeting durations (in minutes)
    melissa_min_duration = 105
    anthony_min_duration = 60
    rebecca_min_duration = 105

    # Constraints for Melissa
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)
    s.add(melissa_end == melissa_start + melissa_min_duration)
    # Melissa is the first meeting, starting after arrival and travel to North Beach
    s.add(melissa_start >= arrival_time + sunset_to_north_beach)

    # Constraints for Anthony
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(anthony_end == anthony_start + anthony_min_duration)
    # Travel from North Beach to Chinatown after Melissa
    s.add(anthony_start >= melissa_end + north_beach_to_chinatown)

    # Constraints for Rebecca
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_end <= rebecca_available_end)
    s.add(rebecca_end == rebecca_start + rebecca_min_duration)
    # Travel from Chinatown to Russian Hill after Anthony
    s.add(rebecca_start >= anthony_end + chinatown_to_russian_hill)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert model values to readable times
        def minutes_to_time(minutes):
            hours = int(minutes) // 60
            mins = int(minutes) % 60
            return f"{hours}:{mins:02d}"

        melissa_s = m.eval(melissa_start).as_decimal(5)
        anthony_s = m.eval(anthony_start).as_decimal(5)
        rebecca_s = m.eval(rebecca_start).as_decimal(5)

        print("SOLUTION:")
        print(f"Meet Melissa at North Beach from {minutes_to_time(float(melissa_s))} to {minutes_to_time(float(melissa_s) + melissa_min_duration)}")
        print(f"Meet Anthony at Chinatown from {minutes_to_time(float(anthony_s))} to {minutes_to_time(float(anthony_s) + anthony_min_duration)}")
        print(f"Meet Rebecca at Russian Hill from {minutes_to_time(float(rebecca_s))} to {minutes_to_time(float(rebecca_s) + rebecca_min_duration)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()