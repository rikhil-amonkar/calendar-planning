from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Time variables in minutes since 9:00 AM
    michelle_start = Int('michelle_start')
    michelle_end = Int('michelle_end')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')
    george_start = Int('george_start')
    george_end = Int('george_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Availability windows in minutes since 9:00 AM
    michelle_available_start = -45  # 8:15 AM is 45 minutes before 9:00 AM
    michelle_available_end = 300    # 2:00 PM is 300 minutes after 9:00 AM
    robert_available_start = 0
    robert_available_end = 285      # 1:45 PM is 285 minutes
    george_available_start = 90     # 10:30 AM is 90 minutes
    george_available_end = 585      # 6:45 PM is 585 minutes
    william_available_start = 570   # 6:30 PM is 570 minutes
    william_available_end = 705     # 8:45 PM is 705 minutes

    # Minimum durations
    michelle_min_duration = 15
    robert_min_duration = 30
    george_min_duration = 30
    william_min_duration = 105

    # Constraints for each meeting
    s.add(michelle_start >= michelle_available_start)
    s.add(michelle_end <= michelle_available_end)
    s.add(michelle_end - michelle_start >= michelle_min_duration)

    s.add(robert_start >= robert_available_start)
    s.add(robert_end <= robert_available_end)
    s.add(robert_end - robert_start >= robert_min_duration)

    s.add(george_start >= george_available_start)
    s.add(george_end <= george_available_end)
    s.add(george_end - george_start >= george_min_duration)

    s.add(william_start >= william_available_start)
    s.add(william_end <= william_available_end)
    s.add(william_end - william_start >= william_min_duration)

    # Starting at Sunset District at time 0 (9:00 AM)
    # Assume the order is Michelle (Chinatown), Robert (Fisherman's Wharf), George (Presidio), William (Russian Hill)
    # Travel times:
    # Sunset to Chinatown: 30 minutes
    s.add(michelle_start >= 30)
    # Chinatown to Fisherman's Wharf: 8 minutes
    s.add(robert_start >= michelle_end + 8)
    # Fisherman's Wharf to Presidio: 17 minutes
    s.add(george_start >= robert_end + 17)
    # Presidio to Russian Hill: 14 minutes
    s.add(william_start >= george_end + 14)

    if s.check() == sat:
        model = s.model()
        michelle_s = model.eval(michelle_start).as_long()
        michelle_e = model.eval(michelle_end).as_long()
        robert_s = model.eval(robert_start).as_long()
        robert_e = model.eval(robert_end).as_long()
        george_s = model.eval(george_start).as_long()
        george_e = model.eval(george_end).as_long()
        william_s = model.eval(william_start).as_long()
        william_e = model.eval(william_end).as_long()

        def minutes_to_time(m):
            hours = 9 + m // 60
            minutes = m % 60
            return f"{hours:02d}:{minutes:02d}"

        itinerary = [
            {"action": "meet", "person": "Michelle", "start_time": minutes_to_time(michelle_s), "end_time": minutes_to_time(michelle_e)},
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(robert_s), "end_time": minutes_to_time(robert_e)},
            {"action": "meet", "person": "George", "start_time": minutes_to_time(george_s), "end_time": minutes_to_time(george_e)},
            {"action": "meet", "person": "William", "start_time": minutes_to_time(william_s), "end_time": minutes_to_time(william_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))