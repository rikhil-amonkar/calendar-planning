from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define locations and friends
    locations = ['Union Square', 'Nob Hill', 'Haight-Ashbury', 'Chinatown', 'Marina District']
    friends = {
        'Karen': {'location': 'Nob Hill', 'start_available': 21*60 + 15, 'end_available': 21*60 + 45, 'min_duration': 30},
        'Joseph': {'location': 'Haight-Ashbury', 'start_available': 12*60 + 30, 'end_available': 19*60 + 45, 'min_duration': 90},
        'Sandra': {'location': 'Chinatown', 'start_available': 7*60 + 15, 'end_available': 19*60 + 15, 'min_duration': 75},
        'Nancy': {'location': 'Marina District', 'start_available': 11*60 + 0, 'end_available': 20*60 + 15, 'min_duration': 105}
    }

    # Travel times dictionary: from_loc -> to_loc -> minutes
    travel_times = {
        'Union Square': {
            'Nob Hill': 9,
            'Haight-Ashbury': 18,
            'Chinatown': 7,
            'Marina District': 18
        },
        'Nob Hill': {
            'Union Square': 7,
            'Haight-Ashbury': 13,
            'Chinatown': 6,
            'Marina District': 11
        },
        'Haight-Ashbury': {
            'Union Square': 17,
            'Nob Hill': 15,
            'Chinatown': 19,
            'Marina District': 17
        },
        'Chinatown': {
            'Union Square': 7,
            'Nob Hill': 8,
            'Haight-Ashbury': 19,
            'Marina District': 12
        },
        'Marina District': {
            'Union Square': 16,
            'Nob Hill': 12,
            'Haight-Ashbury': 16,
            'Chinatown': 16
        }
    }

    # Variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    start_vars = {}
    end_vars = {}
    for friend in friends:
        start_vars[friend] = Int(f'start_{friend}')
        end_vars[friend] = Int(f'end_{friend}')

    # Current time starts at 9:00 AM (0 minutes since 9:00 AM)
    current_time = 0
    current_location = 'Union Square'

    # To determine the order of meetings, we need to model the sequence.
    # This is complex, so we'll assume a feasible order and check constraints.
    # Alternatively, we can use a fixed order that allows all meetings.
    # Here, we'll try meeting Sandra, then Nancy, then Joseph, then Karen.

    # Define the order: Sandra, Nancy, Joseph, Karen
    order = ['Sandra', 'Nancy', 'Joseph', 'Karen']

    # Constraints for each friend in order
    prev_end = 0  # starts at 9:00 AM (0 minutes)
    prev_loc = 'Union Square'
    itinerary = []

    for friend in order:
        data = friends[friend]
        start = start_vars[friend]
        end = end_vars[friend]
        loc = data['location']
        travel_time = travel_times[prev_loc][loc]

        # Start time is after previous end time + travel time
        s.add(start >= prev_end + travel_time)
        # Meeting duration
        s.add(end == start + data['min_duration'])
        # Within availability window
        s.add(start >= data['start_available'] - 9*60)  # convert to since 9:00 AM
        s.add(end <= data['end_available'] - 9*60)

        prev_end = end
        prev_loc = loc

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in order:
            data = friends[friend]
            start_min = model.evaluate(start_vars[friend]).as_long()
            end_min = model.evaluate(end_vars[friend]).as_long()
            start_hour = (start_min + 9*60) // 60
            start_minute = (start_min + 9*60) % 60
            end_hour = (end_min + 9*60) // 60
            end_minute = (end_min + 9*60) % 60
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(result)