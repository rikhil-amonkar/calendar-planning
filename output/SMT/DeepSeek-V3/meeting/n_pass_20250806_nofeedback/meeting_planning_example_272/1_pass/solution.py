from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Timothy at Embarcadero
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')

    # Meeting with Ashley at Mission District
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')

    # Meeting with Patricia at Nob Hill
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Constraints for Timothy (9:45 AM to 5:45 PM)
    s.add(timothy_start >= 45)  # 9:45 AM is 45 minutes after 9:00 AM
    s.add(timothy_end <= 525)   # 5:45 PM is 525 minutes after 9:00 AM (9*60 + 45 = 585 - 60 = 525)
    s.add(timothy_end - timothy_start >= 120)  # Minimum 120 minutes

    # Constraints for Ashley (8:30 PM to 9:15 PM)
    ashley_available_start = 690  # 8:30 PM is 11.5 hours after 9:00 AM (11*60 + 30 = 690)
    ashley_available_end = 705     # 9:15 PM is 705 minutes after 9:00 AM
    s.add(ashley_start >= ashley_available_start)
    s.add(ashley_end <= ashley_available_end)
    s.add(ashley_end - ashley_start >= 45)  # Minimum 45 minutes

    # Constraints for Patricia (6:30 PM to 9:45 PM)
    patricia_available_start = 570  # 6:30 PM is 9.5 hours after 9:00 AM (9*60 + 30 = 570)
    patricia_available_end = 645    # 9:45 PM is 645 minutes after 9:00 AM
    s.add(patricia_start >= patricia_available_start)
    s.add(patricia_end <= patricia_available_end)
    s.add(patricia_end - patricia_start >= 90)  # Minimum 90 minutes

    # Initial location: Russian Hill at time 0 (9:00 AM)
    # We need to sequence the meetings considering travel times
    # Possible sequences: Timothy -> Ashley -> Patricia, or others.

    # Let's assume the order is Timothy -> Patricia -> Ashley
    # Travel from Russian Hill to Embarcadero: 8 minutes
    s.add(timothy_start >= 8)  # arrive at Embarcadero by 9:08 AM, but Timothy is available from 9:45 AM
    # So, the earliest we can meet Timothy is 9:45 AM (45 minutes after 9:00 AM)
    s.add(timothy_start >= 45)

    # After meeting Timothy, travel to next location.
    # Options: go to Patricia (Nob Hill) or Ashley (Mission District)
    # Patricia's availability starts at 6:30 PM (570 minutes), so after meeting Timothy (end by 525 + x), we have time to travel.

    # Suppose we go to Patricia next. Travel from Embarcadero to Nob Hill: 10 minutes
    s.add(patricia_start >= timothy_end + 10)

    # Then, after Patricia, go to Ashley. Travel from Nob Hill to Mission District: 13 minutes
    s.add(ashley_start >= patricia_end + 13)

    # Check if this sequence is possible
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        timothy_start_time = minutes_to_time(m[timothy_start].as_long())
        timothy_end_time = minutes_to_time(m[timothy_end].as_long())
        patricia_start_time = minutes_to_time(m[patricia_start].as_long())
        patricia_end_time = minutes_to_time(m[patricia_end].as_long())
        ashley_start_time = minutes_to_time(m[ashley_start].as_long())
        ashley_end_time = minutes_to_time(m[ashley_end].as_long())

        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": timothy_start_time, "end_time": timothy_end_time},
            {"action": "meet", "person": "Patricia", "start_time": patricia_start_time, "end_time": patricia_end_time},
            {"action": "meet", "person": "Ashley", "start_time": ashley_start_time, "end_time": ashley_end_time}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))