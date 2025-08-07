from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Convert all times to minutes past 9:00 AM (540 minutes since midnight)
    andrew_start = Int('andrew_start')
    andrew_end = Int('andrew_end')
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Convert friends' availability windows to minutes since 9:00 AM
    # Andrew: 11:45 AM (2h45m after 9:00 AM) to 2:30 PM (5h30m after)
    andrew_min_start = (11*60 + 45) - (9*60)  # 165 minutes after 9:00 AM
    andrew_max_end = (14*60 + 30) - (9*60)    # 330 minutes after 9:00 AM

    # Sarah: 4:15 PM (7h15m after 9:00 AM) to 6:45 PM (9h45m after)
    sarah_min_start = (16*60 + 15) - (9*60)   # 435 minutes after 9:00 AM
    sarah_max_end = (18*60 + 45) - (9*60)     # 585 minutes after 9:00 AM

    # Nancy: 5:30 PM (8h30m after 9:00 AM) to 7:15 PM (10h15m after)
    nancy_min_start = (17*60 + 30) - (9*60)   # 510 minutes after 9:00 AM
    nancy_max_end = (19*60 + 15) - (9*60)     # 615 minutes after 9:00 AM

    # Rebecca: 9:45 AM (45m after 9:00 AM) to 9:30 PM (12h30m after)
    rebecca_min_start = (9*60 + 45) - (9*60)  # 45 minutes after 9:00 AM
    rebecca_max_end = (21*60 + 30) - (9*60)   # 750 minutes after 9:00 AM

    # Robert: 8:30 AM (before 9:00 AM, but earliest possible is 9:00 AM) to 2:15 PM (5h15m after)
    robert_min_start = 0  # since 9:00 AM is the earliest possible start
    robert_max_end = (14*60 + 15) - (9*60)    # 315 minutes after 9:00 AM

    # Add constraints for each meeting's duration and availability window
    s.add(andrew_start >= andrew_min_start)
    s.add(andrew_end <= andrew_max_end)
    s.add(andrew_end - andrew_start >= 75)  # 75 minutes

    s.add(sarah_start >= sarah_min_start)
    s.add(sarah_end <= sarah_max_end)
    s.add(sarah_end - sarah_start >= 15)    # 15 minutes

    s.add(nancy_start >= nancy_min_start)
    s.add(nancy_end <= nancy_max_end)
    s.add(nancy_end - nancy_start >= 60)    # 60 minutes

    s.add(rebecca_start >= rebecca_min_start)
    s.add(rebecca_end <= rebecca_max_end)
    s.add(rebecca_end - rebecca_start >= 90) # 90 minutes

    s.add(robert_start >= robert_min_start)
    s.add(robert_end <= robert_max_end)
    s.add(robert_end - robert_start >= 30)   # 30 minutes

    # Define the order of meetings and travel times
    # We need to sequence the meetings such that travel times are accounted for.
    # The order can be flexible, so we'll try to find a feasible sequence.
    # Let's assume the order is: Rebecca -> Robert -> Andrew -> Sarah -> Nancy
    # But this is just a hypothesis; the solver will find a feasible order.

    # To model the sequence, we can use auxiliary variables to represent the order or enforce constraints between meetings.

    # For simplicity, let's assume the following order:
    # 1. Meet Rebecca first (since she's available earliest)
    # 2. Then meet Robert (before his window closes)
    # 3. Then meet Andrew
    # 4. Then meet Sarah
    # 5. Then meet Nancy

    # Travel times:
    # From Union Square to Chinatown (Rebecca): 7 minutes (but starting at 9:00 AM)
    # So Rebecca's meeting can start at 9:00 + 7 = 9:07 AM earliest.
    s.add(rebecca_start >= 7)  # 7 minutes to travel to Chinatown

    # After Rebecca, travel to The Castro (Robert): from Chinatown to The Castro: 20 minutes
    s.add(robert_start >= rebecca_end + 20)

    # After Robert, travel to Golden Gate Park (Andrew): from The Castro to Golden Gate Park: 11 minutes
    s.add(andrew_start >= robert_end + 11)

    # After Andrew, travel to Pacific Heights (Sarah): from Golden Gate Park to Pacific Heights: 16 minutes
    s.add(sarah_start >= andrew_end + 16)

    # After Sarah, travel to Presidio (Nancy): from Pacific Heights to Presidio: 11 minutes
    s.add(nancy_start >= sarah_end + 11)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Rebecca", "start_time": minutes_to_time(m[rebecca_start].as_long()), "end_time": minutes_to_time(m[rebecca_end].as_long())},
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(m[robert_start].as_long()), "end_time": minutes_to_time(m[robert_end].as_long())},
            {"action": "meet", "person": "Andrew", "start_time": minutes_to_time(m[andrew_start].as_long()), "end_time": minutes_to_time(m[andrew_end].as_long())},
            {"action": "meet", "person": "Sarah", "start_time": minutes_to_time(m[sarah_start].as_long()), "end_time": minutes_to_time(m[sarah_end].as_long())},
            {"action": "meet", "person": "Nancy", "start_time": minutes_to_time(m[nancy_start].as_long()), "end_time": minutes_to_time(m[nancy_end].as_long())}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))