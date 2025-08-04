from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')

    # Meeting time windows (converted to minutes since 9:00 AM)
    # Carol: 10:15-11:45 (75-165 mins)
    s.add(carol_start >= 75)
    s.add(carol_end <= 165)
    s.add(carol_end - carol_start >= 30)  # Min 30 mins

    # Karen: 12:45-15:00 (225-360 mins)
    s.add(karen_start >= 225)
    s.add(karen_end <= 360)
    s.add(karen_end - karen_start >= 120)  # Min 120 mins

    # Rebecca: 11:30-20:15 (150-675 mins)
    s.add(rebecca_start >= 150)
    s.add(rebecca_end <= 675)
    s.add(rebecca_end - rebecca_start >= 120)  # Min 120 mins

    # Travel times (in minutes)
    travel_times = {
        ('Union Square', 'Sunset District'): 26,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Mission District'): 13,
    }

    # We'll try both possible meeting orders and see which one works

    # Option 1: Carol -> Rebecca -> Karen
    option1 = And(
        # Start at Union Square at 9:00 (time = 0)
        # Travel to Sunset District (26 mins)
        carol_start == 26,
        # Travel from Sunset to Mission (24 mins)
        rebecca_start >= carol_end + 24,
        # Travel from Mission to Bayview (15 mins)
        karen_start >= rebecca_end + 15,
    )

    # Option 2: Carol -> Karen -> Rebecca
    option2 = And(
        # Start at Union Square at 9:00 (time = 0)
        # Travel to Sunset District (26 mins)
        carol_start == 26,
        # Travel from Sunset to Bayview (22 mins)
        karen_start >= carol_end + 22,
        # Travel from Bayview to Mission (13 mins)
        rebecca_start >= karen_end + 13,
    )

    # Try both options
    s.add(Or(option1, option2))

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
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing constraints
        # First try reducing Carol's meeting time to minimum
        s.push()
        s.add(carol_end - carol_start == 30)
        if s.check() == sat:
            m = s.model()
            # Get the times
            carol_s = m.eval(carol_start).as_long()
            carol_e = m.eval(carol_end).as_long()
            karen_s = m.eval(karen_start).as_long()
            karen_e = m.eval(karen_end).as_long()
            rebecca_s = m.eval(rebecca_start).as_long()
            rebecca_e = m.eval(rebecca_end).as_long()

            itinerary = [
                {"action": "meet", "person": "Carol", "start_time": minutes_to_time(carol_s), "end_time": minutes_to_time(carol_e)},
                {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_s), "end_time": minutes_to_time(karen_e)},
                {"action": "meet", "person": "Rebecca", "start_time": minutes_to_time(rebecca_s), "end_time": minutes_to_time(rebecca_e)}
            ]
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}
        s.pop()

        # If still no solution, try reducing Rebecca's meeting time to minimum
        s.push()
        s.add(rebecca_end - rebecca_start == 120)
        if s.check() == sat:
            m = s.model()
            # Get the times
            carol_s = m.eval(carol_start).as_long()
            carol_e = m.eval(carol_end).as_long()
            karen_s = m.eval(karen_start).as_long()
            karen_e = m.eval(karen_end).as_long()
            rebecca_s = m.eval(rebecca_start).as_long()
            rebecca_e = m.eval(rebecca_end).as_long()

            itinerary = [
                {"action": "meet", "person": "Carol", "start_time": minutes_to_time(carol_s), "end_time": minutes_to_time(carol_e)},
                {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_s), "end_time": minutes_to_time(karen_e)},
                {"action": "meet", "person": "Rebecca", "start_time": minutes_to_time(rebecca_s), "end_time": minutes_to_time(rebecca_e)}
            ]
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}
        s.pop()

        # If still no solution, return empty itinerary
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(solution)