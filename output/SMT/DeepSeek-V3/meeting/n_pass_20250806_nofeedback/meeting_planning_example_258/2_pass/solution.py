from z3 import *
import datetime

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Meeting durations in minutes
    betty_min_duration = 45
    david_min_duration = 90
    barbara_min_duration = 120

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # Subtract 540 to get minutes since 9:00 AM

    # Friends' availability windows in minutes since 9:00 AM
    betty_start = time_to_minutes("10:15")  # 10:15 AM is 75 minutes after 9:00 AM
    betty_end = time_to_minutes("21:30")    # 9:30 PM is 750 minutes after 9:00 AM
    david_start = time_to_minutes("13:00")  # 1:00 PM is 240 minutes after 9:00 AM
    david_end = time_to_minutes("20:15")    # 8:15 PM is 675 minutes after 9:00 AM
    barbara_start = time_to_minutes("09:15")  # 9:15 AM is 15 minutes after 9:00 AM
    barbara_end = time_to_minutes("20:15")    # 8:15 PM is 675 minutes after 9:00 AM

    # Travel times between locations (in minutes)
    travel_times = {
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
    }

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    betty_start_time = Int('betty_start_time')
    betty_end_time = Int('betty_end_time')
    david_start_time = Int('david_start_time')
    david_end_time = Int('david_end_time')
    barbara_start_time = Int('barbara_start_time')
    barbara_end_time = Int('barbara_end_time')

    # Constraints for each meeting's time window and duration
    s.add(betty_start_time >= betty_start)
    s.add(betty_end_time <= betty_end)
    s.add(betty_end_time >= betty_start_time + betty_min_duration)

    s.add(david_start_time >= david_start)
    s.add(david_end_time <= david_end)
    s.add(david_end_time >= david_start_time + david_min_duration)

    s.add(barbara_start_time >= barbara_start)
    s.add(barbara_end_time <= barbara_end)
    s.add(barbara_end_time >= barbara_start_time + barbara_min_duration)

    # Initial location is Embarcadero at time 0 (9:00 AM)
    # The order of meetings is not fixed. We need to ensure that travel times are accounted for between consecutive meetings.
    # We'll model the possibility of meeting Betty, David, and Barbara in some order, with travel times between.
    # Since there are 3 friends, there are 3! = 6 possible orders.
    # We'll use auxiliary variables to represent the order.

    # Let's create variables to represent the order.
    # We'll use three integers to represent the positions of each meeting (1, 2, 3)
    betty_order = Int('betty_order')
    david_order = Int('david_order')
    barbara_order = Int('barbara_order')

    # Each order variable must be 1, 2, or 3
    s.add(betty_order >= 1, betty_order <= 3)
    s.add(david_order >= 1, david_order <= 3)
    s.add(barbara_order >= 1, barbara_order <= 3)

    # All order variables must be distinct
    s.add(Distinct(betty_order, david_order, barbara_order))

    # Locations:
    betty_loc = 'Presidio'
    david_loc = 'Richmond District'
    barbara_loc = 'Fisherman\'s Wharf'

    # Travel time functions
    def get_travel_time(loc1, loc2):
        return travel_times.get((loc1, loc2), 1000)  # Default large value if path doesn't exist (shouldn't happen here)

    # Constraints for order:
    # If betty comes before david in the order, then david's start time >= betty's end time + travel from betty's location to david's.
    s.add(Implies(betty_order < david_order, david_start_time >= betty_end_time + get_travel_time(betty_loc, david_loc)))
    s.add(Implies(david_order < betty_order, betty_start_time >= david_end_time + get_travel_time(david_loc, betty_loc)))

    s.add(Implies(betty_order < barbara_order, barbara_start_time >= betty_end_time + get_travel_time(betty_loc, barbara_loc)))
    s.add(Implies(barbara_order < betty_order, betty_start_time >= barbara_end_time + get_travel_time(barbara_loc, betty_loc)))

    s.add(Implies(david_order < barbara_order, barbara_start_time >= david_end_time + get_travel_time(david_loc, barbara_loc)))
    s.add(Implies(barbara_order < david_order, david_start_time >= barbara_end_time + get_travel_time(barbara_loc, david_loc)))

    # The first meeting must start after the initial location (Embarcadero) and travel time to the first meeting's location.
    # The initial time is 0 (9:00 AM), and the first meeting's start time >= travel time from Embarcadero to the first location.
    first_meeting_start = Int('first_meeting_start')
    s.add(Or(
        And(betty_order == 1, first_meeting_start == betty_start_time, first_meeting_start >= get_travel_time('Embarcadero', betty_loc)),
        And(david_order == 1, first_meeting_start == david_start_time, first_meeting_start >= get_travel_time('Embarcadero', david_loc)),
        And(barbara_order == 1, first_meeting_start == barbara_start_time, first_meeting_start >= get_travel_time('Embarcadero', barbara_loc))
    ))

    # To maximize the number of friends met, we need to ensure all meetings are scheduled.
    # Alternatively, we could add a constraint that all meetings must be scheduled, but since the problem says "as many as possible", but the constraints seem to allow meeting all three.

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Retrieve the meeting times
        betty_s = m.eval(betty_start_time).as_long()
        betty_e = m.eval(betty_end_time).as_long()
        david_s = m.eval(david_start_time).as_long()
        david_e = m.eval(david_end_time).as_long()
        barbara_s = m.eval(barbara_start_time).as_long()
        barbara_e = m.eval(barbara_end_time).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight.
            hh = total_minutes // 60
            mm = total_minutes % 60
            return f"{hh:02d}:{mm:02d}"

        itinerary = []
        # Determine the order of meetings based on the model's order variables
        betty_o = m.eval(betty_order).as_long()
        david_o = m.eval(david_order).as_long()
        barbara_o = m.eval(barbara_order).as_long()

        # Create a list of meetings with their order and times
        meetings = [
            (betty_o, "Betty", betty_s, betty_e),
            (david_o, "David", david_s, david_e),
            (barbara_o, "Barbara", barbara_s, barbara_e),
        ]

        # Sort meetings by order
        meetings.sort()

        # Add to itinerary in order
        for order, person, start, end in meetings:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}  # No solution found

result = solve_scheduling()
print(result)