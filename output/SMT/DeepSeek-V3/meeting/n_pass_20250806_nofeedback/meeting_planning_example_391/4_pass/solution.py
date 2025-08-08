from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Convert all times to minutes since midnight
    def time_to_min(h, m):
        return h * 60 + m

    # Meeting durations in minutes
    kevin_duration = 75
    kimberly_duration = 30
    joseph_duration = 45
    thomas_duration = 45

    # Define time variables for each meeting (start times)
    kevin_start = Int('kevin_start')
    kimberly_start = Int('kimberly_start')
    joseph_start = Int('joseph_start')
    thomas_start = Int('thomas_start')

    # Add constraints for each friend's availability
    # Kevin: 8:15AM (495) to 9:30PM (1290)
    s.add(kevin_start >= time_to_min(8, 15))
    s.add(kevin_start + kevin_duration <= time_to_min(21, 30))

    # Kimberly: 8:45AM (525) to 12:30PM (750)
    s.add(kimberly_start >= time_to_min(8, 45))
    s.add(kimberly_start + kimberly_duration <= time_to_min(12, 30))

    # Joseph: 6:30PM (1170) to 7:15PM (1185)
    s.add(joseph_start >= time_to_min(18, 30))
    s.add(joseph_start + joseph_duration <= time_to_min(19, 15))

    # Thomas: 7:00PM (1200) to 9:45PM (1305)
    s.add(thomas_start >= time_to_min(19, 0))
    s.add(thomas_start + thomas_duration <= time_to_min(21, 45))

    # Starting at Sunset District at 9:00AM (540)
    current_time = time_to_min(9, 0)

    # Try meeting Kimberly first since her window is earliest and shortest
    # Travel to Kimberly: Sunset to Russian Hill (24 min)
    s.add(kimberly_start >= current_time + 24)
    current_time = kimberly_start + kimberly_duration

    # Travel to Kevin: Russian Hill to Alamo Square (15 min)
    s.add(kevin_start >= current_time + 15)
    current_time = kevin_start + kevin_duration

    # Travel to Joseph: Alamo Square to Presidio (18 min)
    s.add(joseph_start >= current_time + 18)
    current_time = joseph_start + joseph_duration

    # Travel to Thomas: Presidio to Financial District (22 min)
    s.add(thomas_start >= current_time + 22)

    if s.check() == sat:
        m = s.model()
        itinerary = []

        def format_time(minutes):
            return f"{minutes//60:02d}:{minutes%60:02d}"

        # Verify all meetings fit within their windows
        kim_start = m[kimberly_start].as_long()
        if not (time_to_min(8, 45) <= kim_start <= time_to_min(12, 30) - kimberly_duration:
            return {"itinerary": []}

        kev_start = m[kevin_start].as_long()
        if not (time_to_min(8, 15) <= kev_start <= time_to_min(21, 30) - kevin_duration:
            return {"itinerary": []}

        jos_start = m[joseph_start].as_long()
        if not (time_to_min(18, 30) <= jos_start <= time_to_min(19, 15) - joseph_duration:
            return {"itinerary": []}

        tho_start = m[thomas_start].as_long()
        if not (time_to_min(19, 0) <= tho_start <= time_to_min(21, 45) - thomas_duration:
            return {"itinerary": []}

        itinerary.append({
            "action": "meet",
            "person": "Kimberly",
            "start_time": format_time(kim_start),
            "end_time": format_time(kim_start + kimberly_duration)
        })

        itinerary.append({
            "action": "meet",
            "person": "Kevin",
            "start_time": format_time(kev_start),
            "end_time": format_time(kev_start + kevin_duration)
        })

        itinerary.append({
            "action": "meet",
            "person": "Joseph",
            "start_time": format_time(jos_start),
            "end_time": format_time(jos_start + joseph_duration)
        })

        itinerary.append({
            "action": "meet",
            "person": "Thomas",
            "start_time": format_time(tho_start),
            "end_time": format_time(tho_start + thomas_duration)
        })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))