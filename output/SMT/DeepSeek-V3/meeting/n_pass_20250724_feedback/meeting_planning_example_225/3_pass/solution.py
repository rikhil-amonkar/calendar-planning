from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')

    # Convert friend availability windows to minutes since 9:00 AM
    # Sarah: 4:00 PM to 6:15 PM (16:00 to 18:15) -> 420 to 555 minutes (since 9:00 AM is 0)
    sarah_available_start = 16 * 60 - 9 * 60  # 7 hours * 60 = 420 minutes
    sarah_available_end = 18 * 60 + 15 - 9 * 60  # 555 minutes
    # Jeffrey: 3:00 PM to 10:00 PM (15:00 to 22:00) -> 360 to 780 minutes
    jeffrey_available_start = 15 * 60 - 9 * 60  # 360 minutes
    jeffrey_available_end = 22 * 60 - 9 * 60  # 780 minutes
    # Brian: 4:00 PM to 5:30 PM (16:00 to 17:30) -> 420 to 510 minutes
    brian_available_start = 16 * 60 - 9 * 60  # 420 minutes
    brian_available_end = 17 * 60 + 30 - 9 * 60  # 510 minutes

    # Meeting durations in minutes
    sarah_duration = 60
    jeffrey_duration = 75
    brian_duration = 75

    # Add constraints for each meeting's duration and availability
    s.add(sarah_start >= sarah_available_start)
    s.add(sarah_end <= sarah_available_end)
    s.add(sarah_end == sarah_start + sarah_duration)

    s.add(jeffrey_start >= jeffrey_available_start)
    s.add(jeffrey_end <= jeffrey_available_end)
    s.add(jeffrey_end == jeffrey_start + jeffrey_duration)

    s.add(brian_start >= brian_available_start)
    s.add(brian_end <= brian_available_end)
    s.add(brian_end == brian_start + brian_duration)

    # Travel times between locations (in minutes)
    travel_times = {
        ('Sunset District', 'North Beach'): 29,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Alamo Square'): 16,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Alamo Square'): 15,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Union Square'): 14,
    }

    # Define the order of meetings
    # We'll try all possible permutations of the order of meetings
    # and add constraints based on the order
    orders = [
        ['Jeffrey', 'Sarah', 'Brian'],
        ['Jeffrey', 'Brian', 'Sarah'],
        ['Sarah', 'Jeffrey', 'Brian'],
        ['Sarah', 'Brian', 'Jeffrey'],
        ['Brian', 'Jeffrey', 'Sarah'],
        ['Brian', 'Sarah', 'Jeffrey']
    ]

    # Function to get location by name
    def get_location(name):
        if name == 'Sarah':
            return 'North Beach'
        elif name == 'Jeffrey':
            return 'Union Square'
        elif name == 'Brian':
            return 'Alamo Square'

    # Function to get start and end variables by name
    def get_vars(name):
        if name == 'Sarah':
            return sarah_start, sarah_end
        elif name == 'Jeffrey':
            return jeffrey_start, jeffrey_end
        elif name == 'Brian':
            return brian_start, brian_end

    # Try each order
    for order in orders:
        # Create a temporary solver for this order
        temp_s = Solver()
        temp_s.add(s.assertions())

        # Initial location is Sunset District
        current_location = 'Sunset District'
        current_time = 0  # 9:00 AM is 0 minutes

        # Process each meeting in order
        for i, name in enumerate(order):
            start_var, end_var = get_vars(name)
            location = get_location(name)

            # Travel time to the current meeting location
            travel_time = travel_times.get((current_location, location), None)
            if travel_time is None:
                travel_time = travel_times.get((location, current_location), None)
                if travel_time is None:
                    break  # No travel time found, skip this order

            # Arrival time at the meeting location
            arrival_time = current_time + travel_time

            # Meeting must start after arrival time and within availability
            temp_s.add(start_var >= arrival_time)

            # Update current time to the end of the meeting
            current_time = end_var
            current_location = location

        # Check if this order is feasible
        if temp_s.check() == sat:
            m = temp_s.model()
            # Extract start and end times
            js = m.eval(jeffrey_start).as_long()
            je = m.eval(jeffrey_end).as_long()
            ss = m.eval(sarah_start).as_long()
            se = m.eval(sarah_end).as_long()
            bs = m.eval(brian_start).as_long()
            be = m.eval(brian_end).as_long()

            # Convert minutes back to HH:MM format (from 9:00 AM base)
            def to_time_str(minutes):
                hours = 9 + minutes // 60
                mins = minutes % 60
                return f"{hours:02d}:{mins:02d}"

            jeffrey_start_str = to_time_str(js)
            jeffrey_end_str = to_time_str(je)
            sarah_start_str = to_time_str(ss)
            sarah_end_str = to_time_str(se)
            brian_start_str = to_time_str(bs)
            brian_end_str = to_time_str(be)

            # Create itinerary
            itinerary = [
                {"action": "meet", "person": "Jeffrey", "start_time": jeffrey_start_str, "end_time": jeffrey_end_str},
                {"action": "meet", "person": "Sarah", "start_time": sarah_start_str, "end_time": sarah_end_str},
                {"action": "meet", "person": "Brian", "start_time": brian_start_str, "end_time": brian_end_str}
            ]

            # Sort itinerary by start time
            itinerary.sort(key=lambda x: x['start_time'])

            return {"itinerary": itinerary}

    # If no feasible order found
    return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))