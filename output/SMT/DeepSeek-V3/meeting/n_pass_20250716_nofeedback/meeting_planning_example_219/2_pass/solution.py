from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Time variables in minutes since 9:00 AM (540)
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Emily's availability: 11:45 AM (705) to 3:15 PM (915)
    s.add(emily_start >= 705)  # 11:45 AM
    s.add(emily_end <= 915)    # 3:15 PM
    s.add(emily_end - emily_start >= 105)  # 105 minutes meeting

    # Barbara's availability: 4:45 PM (1005) to 6:15 PM (1095)
    s.add(barbara_start >= 1005)  # 4:45 PM
    s.add(barbara_end <= 1095)    # 6:15 PM
    s.add(barbara_end - barbara_start >= 60)  # 60 minutes meeting

    # William's availability: 5:15 PM (1035) to 7:00 PM (1140)
    s.add(william_start >= 1035)  # 5:15 PM
    s.add(william_end <= 1140)    # 7:00 PM
    s.add(william_end - william_start >= 105)  # 105 minutes meeting

    # Travel times from The Castro to Alamo Square: 8 minutes
    # Start at The Castro at 9:00 AM (540)
    # First meeting is Emily at Alamo Square, starting at earliest 540 + 8 = 548 (9:08 AM)
    # But Emily's window starts at 705 (11:45 AM), so we can arrive at Alamo Square by 705.
    # So, the travel time is already accounted for by the meeting start time.

    # After meeting Emily, travel to next location.
    # Possible next meetings: Barbara at Union Square or William at Chinatown.
    # From Alamo Square:
    # - To Union Square: 14 minutes
    # - To Chinatown: 16 minutes

    # Similarly, after meeting Barbara or William, travel to the next if possible.

    # We need to sequence the meetings. Let's assume the order is Emily -> Barbara -> William.
    # So, after Emily at Alamo Square, travel to Union Square (14 minutes).
    s.add(barbara_start >= emily_end + 14)

    # After Barbara at Union Square, travel to Chinatown (7 minutes).
    s.add(william_start >= barbara_end + 7)

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Emily's meeting
        emily_s = model[emily_start].as_long()
        emily_e = model[emily_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "Emily",
            "start_time": minutes_to_time(emily_s),
            "end_time": minutes_to_time(emily_e)
        })

        # Barbara's meeting
        barbara_s = model[barbara_start].as_long()
        barbara_e = model[barbara_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "Barbara",
            "start_time": minutes_to_time(barbara_s),
            "end_time": minutes_to_time(barbara_e)
        })

        # William's meeting
        william_s = model[william_start].as_long()
        william_e = model[william_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "William",
            "start_time": minutes_to_time(william_s),
            "end_time": minutes_to_time(william_e)
        })

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

# Solve the scheduling problem
result = solve_scheduling()

# Output the result in JSON format
print(json.dumps(result, indent=2))