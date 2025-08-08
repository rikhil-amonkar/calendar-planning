from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define time variables in minutes since 9:00 AM (540 minutes)
    # Meeting with Carol at Sunset District (10:15-11:45, min 30 mins)
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')

    # Meeting with Rebecca at Mission District (11:30-20:15, min 120 mins)
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')

    # Meeting with Karen at Bayview (12:45-15:00, min 120 mins)
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Travel times (in minutes)
    travel = {
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Sunset District'): 26,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Sunset District'): 24,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Sunset District'): 23,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22
    }

    # Convert availability windows to minutes since 9:00 AM (540)
    carol_available_start = 75  # 10:15 is 75 mins after 9:00
    carol_available_end = 165    # 11:45 is 165 mins after 9:00
    rebecca_available_start = 150  # 11:30 is 150 mins after 9:00
    rebecca_available_end = 555    # 20:15 is 555 mins after 9:00
    karen_available_start = 225    # 12:45 is 225 mins after 9:00
    karen_available_end = 360      # 15:00 is 360 mins after 9:00

    # Add constraints for each meeting
    # Carol must meet for at least 30 minutes within 10:15-11:45
    s.add(carol_start >= carol_available_start)
    s.add(carol_end <= carol_available_end)
    s.add(carol_end - carol_start >= 30)

    # Rebecca must meet for at least 120 minutes within 11:30-20:15
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_end <= rebecca_available_end)
    s.add(rebecca_end - rebecca_start >= 120)

    # Karen must meet for at least 120 minutes within 12:45-15:00
    s.add(karen_start >= karen_available_start)
    s.add(karen_end <= karen_available_end)
    s.add(karen_end - karen_start >= 120)

    # Initial location is Union Square at time 0 (9:00 AM)
    # The sequence is: Union Square -> Sunset (Carol) -> Mission (Rebecca) -> Bayview (Karen) or other permutations.

    # We need to model the possible sequences and travel times.
    # Let's consider the possible orders of meetings and choose the feasible one.

    # Option 1: Carol -> Rebecca -> Karen
    # Constraints:
    # 1. Travel from Union Square to Sunset: 26 mins. So Carol's start >= 26.
    s.add(Or(
        And(
            carol_start >= 26,  # travel to Sunset
            rebecca_start >= carol_end + travel[('Sunset District', 'Mission District')],  # travel to Mission
            karen_start >= rebecca_end + travel[('Mission District', 'Bayview')]  # travel to Bayview
        ),
        # Option 2: Carol -> Karen -> Rebecca
        And(
            carol_start >= 26,  # travel to Sunset
            karen_start >= carol_end + travel[('Sunset District', 'Bayview')],  # travel to Bayview
            rebecca_start >= karen_end + travel[('Bayview', 'Mission District')]  # travel to Mission
        ),
        # Option 3: Rebecca -> Carol -> Karen (but Carol's window is before Rebecca's, so likely not feasible)
        # Option 4: Rebecca -> Karen -> Carol (Carol's window is early, likely not feasible after)
        # Option 5: Karen -> Carol -> Rebecca (Carol's window is before Karen's, not feasible)
        # Option 6: Karen -> Rebecca -> Carol (Carol's window is early, not feasible)
    ))

    # The above options cover feasible sequences where Carol's meeting is first.

    # To maximize the number of meetings, we need to ensure all three are scheduled.
    # The solver will find a model where all meetings fit.

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        carol_s = m.eval(carol_start).as_long()
        carol_e = m.eval(carol_end).as_long()
        rebecca_s = m.eval(rebecca_start).as_long()
        rebecca_e = m.eval(rebecca_end).as_long()
        karen_s = m.eval(karen_start).as_long()
        karen_e = m.eval(karen_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": to_time(carol_s), "end_time": to_time(carol_e)},
            {"action": "meet", "person": "Rebecca", "start_time": to_time(rebecca_s), "end_time": to_time(rebecca_e)},
            {"action": "meet", "person": "Karen", "start_time": to_time(karen_s), "end_time": to_time(karen_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))