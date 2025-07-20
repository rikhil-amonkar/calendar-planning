from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    mary_start = Int('mary_start')
    mary_end = Int('mary_end')
    lisa_start = Int('lisa_start')
    lisa_end = Int('lisa_end')
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Constraints for each meeting's duration and availability window
    # Mary: Pacific Heights, 10:00 AM to 7:00 PM, min 45 minutes
    s.add(mary_start >= 60)  # 10:00 AM is 60 minutes after 9:00 AM
    s.add(mary_end <= 600)   # 7:00 PM is 600 minutes after 9:00 AM (10 hours)
    s.add(mary_end - mary_start >= 45)

    # Lisa: Mission District, 8:30 PM to 10:00 PM, min 75 minutes
    s.add(lisa_start >= 690)  # 8:30 PM is 690 minutes after 9:00 AM (11.5 hours)
    s.add(lisa_end <= 780)    # 10:00 PM is 780 minutes after 9:00 AM (13 hours)
    s.add(lisa_end - lisa_start >= 75)

    # Betty: Haight-Ashbury, 7:15 AM to 5:15 PM, min 90 minutes
    # Since we start at 9:00 AM, Betty's window is from 0 (7:15 AM is -105 minutes from 9:00 AM) to 495 (5:15 PM is 8.25 hours after 9:00 AM)
    # But since we start at 9:00 AM, earliest we can meet is 9:00 AM (0 minutes)
    s.add(betty_start >= 0)
    s.add(betty_end <= 495)  # 5:15 PM is 495 minutes after 9:00 AM (8.25 hours)
    s.add(betty_end - betty_start >= 90)

    # Charles: Financial District, 11:15 AM to 3:00 PM, min 120 minutes
    s.add(charles_start >= 135)  # 11:15 AM is 135 minutes after 9:00 AM
    s.add(charles_end <= 360)    # 3:00 PM is 360 minutes after 9:00 AM (6 hours)
    s.add(charles_end - charles_start >= 120)

    # Define the order of meetings and travel times
    # We need to decide the sequence of meetings. Possible sequences are permutations of the four meetings.
    # However, given the tight constraints, we'll try a feasible order manually or encode all possibilities.
    # For simplicity, we'll assume the order: Betty -> Charles -> Mary -> Lisa
    # (This is a heuristic; a complete solution would explore all permutations.)

    # Starting at Bayview at time 0 (9:00 AM)
    # Travel from Bayview to Haight-Ashbury: 19 minutes
    s.add(betty_start >= 19)
    # Travel from Haight-Ashbury to Financial District: 21 minutes
    s.add(charles_start >= betty_end + 21)
    # Travel from Financial District to Pacific Heights: 13 minutes
    s.add(mary_start >= charles_end + 13)
    # Travel from Pacific Heights to Mission District: 15 minutes
    s.add(lisa_start >= mary_end + 15)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Betty", "start_time": minutes_to_time(m[betty_start].as_long()), "end_time": minutes_to_time(m[betty_end].as_long())},
            {"action": "meet", "person": "Charles", "start_time": minutes_to_time(m[charles_start].as_long()), "end_time": minutes_to_time(m[charles_end].as_long())},
            {"action": "meet", "person": "Mary", "start_time": minutes_to_time(m[mary_start].as_long()), "end_time": minutes_to_time(m[mary_end].as_long())},
            {"action": "meet", "person": "Lisa", "start_time": minutes_to_time(m[lisa_start].as_long()), "end_time": minutes_to_time(m[lisa_end].as_long())}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

# Execute the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))