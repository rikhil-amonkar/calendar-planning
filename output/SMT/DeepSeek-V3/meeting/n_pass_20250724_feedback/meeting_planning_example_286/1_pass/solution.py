from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Meet Carol at Sunset District (10:15-11:45, min 30 mins)
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')

    # Meet Karen at Bayview (12:45-15:00, min 120 mins)
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Meet Rebecca at Mission District (11:30-20:15, min 120 mins)
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Carol's window: 10:15-11:45 -> 75 to 165 minutes since 9:00
    s.add(carol_start >= 75)
    s.add(carol_end <= 165)
    s.add(carol_end - carol_start >= 30)

    # Karen's window: 12:45-15:00 -> 225 to 360 minutes since 9:00
    s.add(karen_start >= 225)
    s.add(karen_end <= 360)
    s.add(karen_end - karen_start >= 120)

    # Rebecca's window: 11:30-20:15 -> 150 to 675 minutes since 9:00
    s.add(rebecca_start >= 150)
    s.add(rebecca_end <= 675)
    s.add(rebecca_end - rebecca_start >= 120)

    # Travel constraints
    # Start at Union Square at 9:00 (time = 0)

    # Possible sequences:
    # Option 1: Carol -> Rebecca -> Karen
    # Option 2: Carol -> Karen -> Rebecca
    # Option 3: Rebecca -> Karen -> Carol (but Carol's window is early, so this is impossible)
    # Option 4: Karen -> Rebecca -> Carol (Carol's window is early, so impossible)
    # So only Options 1 and 2 are feasible.

    # We'll model both options and let the solver choose.

    # Option 1: Carol -> Rebecca -> Karen
    # Travel from Union Square to Sunset (26 mins)
    option1_carol_start = 0 + 26
    s.add(Implies(And(carol_start >= option1_carol_start, carol_end <= 165), True))
    # Travel from Sunset to Mission (24 mins)
    option1_rebecca_start_min = carol_end + 24
    s.add(Implies(rebecca_start >= option1_rebecca_start_min, True))
    # Travel from Mission to Bayview (15 mins)
    option1_karen_start_min = rebecca_end + 15
    s.add(Implies(karen_start >= option1_karen_start_min, True))

    # Option 2: Carol -> Karen -> Rebecca
    # Travel from Union Square to Sunset (26 mins)
    option2_carol_start = 0 + 26
    s.add(Implies(And(carol_start >= option2_carol_start, carol_end <= 165), True))
    # Travel from Sunset to Bayview (22 mins)
    option2_karen_start_min = carol_end + 22
    s.add(Implies(karen_start >= option2_karen_start_min, True))
    # Travel from Bayview to Mission (13 mins)
    option2_rebecca_start_min = karen_end + 13
    s.add(Implies(rebecca_start >= option2_rebecca_start_min, True))

    # Ensure no overlaps and all meetings fit
    # The solver will find a model that satisfies all constraints

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Get the times
        carol_s = m.eval(carol_start).as_long()
        carol_e = m.eval(carol_end).as_long()
        karen_s = m.eval(karen_start).as_long()
        karen_e = m.eval(karen_end).as_long()
        rebecca_s = m.eval(rebecca_start).as_long()
        rebecca_e = m.eval(rebecca_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": minutes_to_time(carol_s), "end_time": minutes_to_time(carol_e)},
            {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_s), "end_time": minutes_to_time(karen_e)},
            {"action": "meet", "person": "Rebecca", "start_time": minutes_to_time(rebecca_s), "end_time": minutes_to_time(rebecca_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(solution)