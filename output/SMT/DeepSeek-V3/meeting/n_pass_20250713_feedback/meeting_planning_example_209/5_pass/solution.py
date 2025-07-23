from z3 import *

def solve_scheduling():
    s = Solver()

    # Meeting start times
    melissa_start = Real('melissa_start')
    anthony_start = Real('anthony_start')
    rebecca_start = Real('rebecca_start')

    # Travel times in minutes
    sunset_to_north_beach = 29
    north_beach_to_chinatown = 6
    chinatown_to_russian_hill = 7

    # Arrival time at Sunset District (9:00 AM)
    arrival_time = 540  # minutes

    # Friends' availability windows
    melissa_available_start = 495  # 8:15 AM
    melissa_available_end = 810    # 1:30 PM
    anthony_available_start = 795  # 1:15 PM
    anthony_available_end = 870    # 2:30 PM
    rebecca_available_start = 1170 # 7:30 PM
    rebecca_available_end = 1215   # 9:15 PM

    # Meeting durations (minimum required)
    melissa_duration = 105
    anthony_duration = 60
    rebecca_duration = 105

    # Melissa constraints
    earliest_melissa_start = max(arrival_time + sunset_to_north_beach, melissa_available_start)
    s.add(melissa_start == earliest_melissa_start)  # Start as early as possible
    s.add(melissa_start + melissa_duration <= melissa_available_end)

    # Anthony constraints
    s.add(anthony_start == anthony_available_start)  # Start exactly at 1:15PM
    s.add(anthony_start >= melissa_start + melissa_duration + north_beach_to_chinatown)
    s.add(anthony_start + anthony_duration <= anthony_available_end)

    # Rebecca constraints
    s.add(rebecca_start >= anthony_start + anthony_duration + chinatown_to_russian_hill)
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_start + rebecca_duration <= rebecca_available_end)

    if s.check() == sat:
        m = s.model()
        
        def minutes_to_time(minutes):
            hours = int(minutes) // 60
            mins = int(minutes) % 60
            return f"{hours}:{mins:02d}"

        melissa_s = float(m.eval(melissa_start).as_decimal(5))
        anthony_s = float(m.eval(anthony_start).as_decimal(5))
        rebecca_s = float(m.eval(rebecca_start).as_decimal(5))

        print("SOLUTION:")
        print(f"1. Meet Melissa at North Beach from {minutes_to_time(melissa_s)} to {minutes_to_time(melissa_s + melissa_duration)}")
        print(f"   (Travel time from Sunset: 29 minutes)")
        print(f"2. Travel to Chinatown (6 minutes)")
        print(f"3. Meet Anthony at Chinatown from {minutes_to_time(anthony_s)} to {minutes_to_time(anthony_s + anthony_duration)}")
        print(f"4. Travel to Russian Hill (7 minutes)")
        print(f"5. Meet Rebecca at Russian Hill from {minutes_to_time(rebecca_s)} to {minutes_to_time(rebecca_s + rebecca_duration)}")
    else:
        print("No feasible schedule found that meets all constraints")

solve_scheduling()