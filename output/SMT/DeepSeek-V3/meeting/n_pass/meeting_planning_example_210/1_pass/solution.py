from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Emily at Presidio: 4:15PM to 9:00PM, min 105 minutes
    emily_start = Int('emily_start')  # in minutes from 9:00AM (540)
    emily_end = Int('emily_end')

    # Joseph at Richmond District: 5:15PM to 10:00PM, min 120 minutes
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Melissa at Financial District: 3:45PM to 9:45PM, min 75 minutes
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')

    # Convert all times to minutes since 9:00AM (540 minutes since midnight)
    # Emily's window: 4:15PM is 16*60 +15 = 975 minutes since midnight, 975-540=435 minutes since 9AM
    emily_window_start = 435  # 4:15PM is 435 minutes after 9:00AM
    emily_window_end = 720     # 9:00PM is 720 minutes after 9:00AM (21:00 - 9:00 = 12 hours = 720 minutes)

    # Joseph's window: 5:15PM is 17*60 +15 = 1035 minutes since midnight, 1035-540=495 minutes since 9AM
    joseph_window_start = 495
    joseph_window_end = 780    # 10:00PM is 22:00 -9:00 = 13 hours = 780 minutes

    # Melissa's window: 3:45PM is 15*60 +45 = 945 minutes since midnight, 945-540=405 minutes since 9AM
    melissa_window_start = 405
    melissa_window_end = 765   # 9:45PM is 21:45 -9:00 = 12 hours 45 minutes = 765 minutes

    # Add constraints for each meeting's duration and window
    s.add(emily_start >= emily_window_start)
    s.add(emily_end <= emily_window_end)
    s.add(emily_end - emily_start >= 105)

    s.add(joseph_start >= joseph_window_start)
    s.add(joseph_end <= joseph_window_end)
    s.add(joseph_end - joseph_start >= 120)

    s.add(melissa_start >= melissa_window_start)
    s.add(melissa_end <= melissa_window_end)
    s.add(melissa_end - melissa_start >= 75)

    # Define travel times (in minutes)
    # From Fisherman's Wharf (starting point) to others:
    # FW to Presidio: 17
    # FW to Richmond: 18
    # FW to Financial: 11

    # Travel times between locations:
    travel = {
        ('Fishermans Wharf', 'Presidio'): 17,
        ('Fishermans Wharf', 'Richmond District'): 18,
        ('Fishermans Wharf', 'Financial District'): 11,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
    }

    # We need to model the sequence of meetings and travel times.
    # Let's assume the order is Melissa, Emily, Joseph (but the solver will find the feasible order)
    # We'll need to consider all possible permutations of the three meetings and choose the feasible one.

    # We'll model the problem by considering all possible orders of meetings and adding constraints accordingly.

    # Let's create variables to represent the order.
    # We'll have three meetings: 0 (Melissa), 1 (Emily), 2 (Joseph)
    # The order will be a permutation of [0,1,2]
    # For each possible order, we'll add constraints and check feasibility.

    # Since Z3 doesn't directly handle permutations, we'll need to model the order explicitly.
    # Alternatively, we can try all possible orders in separate solver instances and pick the feasible one.

    # Let's try all possible orders (6 permutations) and find the first feasible one.

    orders = [
        [0, 1, 2],  # Melissa -> Emily -> Joseph
        [0, 2, 1],  # Melissa -> Joseph -> Emily
        [1, 0, 2],  # Emily -> Melissa -> Joseph
        [1, 2, 0],  # Emily -> Joseph -> Melissa
        [2, 0, 1],  # Joseph -> Melissa -> Emily
        [2, 1, 0],  # Joseph -> Emily -> Melissa
    ]

    feasible_solution = None

    for order in orders:
        s_temp = Solver()

        # Add the meeting constraints
        s_temp.add(emily_start >= emily_window_start)
        s_temp.add(emily_end <= emily_window_end)
        s_temp.add(emily_end - emily_start >= 105)

        s_temp.add(joseph_start >= joseph_window_start)
        s_temp.add(joseph_end <= joseph_window_end)
        s_temp.add(joseph_end - joseph_start >= 120)

        s_temp.add(melissa_start >= melissa_window_start)
        s_temp.add(melissa_end <= melissa_window_end)
        s_temp.add(melissa_end - melissa_start >= 75)

        # Variables to track the current location and time
        current_time = 0  # starting at 9:00AM (0 minutes after)
        current_location = 'Fishermans Wharf'

        # Process meetings in the current order
        meetings = []
        for meeting_idx in order:
            if meeting_idx == 0:
                person = 'Melissa'
                location = 'Financial District'
                start = melissa_start
                end = melissa_end
            elif meeting_idx == 1:
                person = 'Emily'
                location = 'Presidio'
                start = emily_start
                end = emily_end
            elif meeting_idx == 2:
                person = 'Joseph'
                location = 'Richmond District'
                start = joseph_start
                end = joseph_end

            # Add travel time from current_location to meeting location
            travel_time = travel.get((current_location, location), 0)
            s_temp.add(start >= current_time + travel_time)

            # Update current_time and location
            current_time = end
            current_location = location

            meetings.append((person, start, end))

        # Check if this order is feasible
        if s_temp.check() == sat:
            model = s_temp.model()
            # Extract the meeting times
            itinerary = []
            for person, start_var, end_var in meetings:
                start_val = model.evaluate(start_var).as_long()
                end_val = model.evaluate(end_var).as_long()
                # Convert minutes since 9:00AM to HH:MM
                start_hh = 9 + start_val // 60
                start_mm = start_val % 60
                end_hh = 9 + end_val // 60
                end_mm = end_val % 60
                start_time = f"{start_hh:02d}:{start_mm:02d}"
                end_time = f"{end_hh:02d}:{end_mm:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": start_time,
                    "end_time": end_time
                })
            feasible_solution = {"itinerary": itinerary}
            break

    if feasible_solution is None:
        return {"itinerary": []}
    else:
        return feasible_solution

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))