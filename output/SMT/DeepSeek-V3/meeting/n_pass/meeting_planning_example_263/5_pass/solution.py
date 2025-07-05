from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since midnight
    # Arrival time at Bayview is 9:00 AM (540 minutes)
    arrival_time = 540

    # Friends' availability in minutes since midnight
    # Betty: Embarcadero 7:45 PM (1170) to 9:45 PM (1305)
    betty_start = 1170
    betty_end = 1305
    betty_min_duration = 15

    # Karen: Fisherman's Wharf 8:45 AM (525) to 3:00 PM (900)
    karen_start = 525
    karen_end = 900
    karen_min_duration = 30

    # Anthony: Financial District 9:15 AM (555) to 9:30 PM (1290)
    anthony_start = 555
    anthony_end = 1290
    anthony_min_duration = 105

    # Travel times in minutes
    bayview_to_fishermans = 25
    fishermans_to_financial = 11
    financial_to_embarcadero = 4

    # Decision variables for meeting times
    karen_meet_start = Int('karen_meet_start')
    karen_meet_end = Int('karen_meet_end')
    anthony_meet_start = Int('anthony_meet_start')
    anthony_meet_end = Int('anthony_meet_end')
    betty_meet_start = Int('betty_meet_start')
    betty_meet_end = Int('betty_meet_end')

    # Constraints for Karen
    s.add(karen_meet_start >= max(karen_start, arrival_time + bayview_to_fishermans))
    s.add(karen_meet_end == karen_meet_start + karen_min_duration)
    s.add(karen_meet_end <= karen_end)

    # Constraints for Anthony
    s.add(anthony_meet_start >= karen_meet_end + fishermans_to_financial)
    s.add(anthony_meet_start >= anthony_start)
    s.add(anthony_meet_end == anthony_meet_start + anthony_min_duration)
    s.add(anthony_meet_end <= anthony_end)

    # Constraints for Betty
    s.add(betty_meet_start >= anthony_meet_end + financial_to_embarcadero)
    s.add(betty_meet_start >= betty_start)  # Ensure meeting starts no earlier than 7:45 PM
    s.add(betty_meet_end == betty_meet_start + betty_min_duration)
    s.add(betty_meet_end <= betty_end)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Karen at Fisherman's Wharf from {m[karen_meet_start].as_long()} to {m[karen_meet_end].as_long()}")
        print(f"Meet Anthony at Financial District from {m[anthony_meet_start].as_long()} to {m[anthony_meet_end].as_long()}")
        print(f"Meet Betty at Embarcadero from {m[betty_meet_start].as_long()} to {m[betty_meet_end].as_long()}")
    else:
        print("No feasible schedule found.")

solve_scheduling()