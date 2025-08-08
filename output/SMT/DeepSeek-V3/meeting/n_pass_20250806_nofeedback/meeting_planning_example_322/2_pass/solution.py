from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define the locations and their travel times
    locations = {
        'Sunset District': 0,
        'Russian Hill': 1,
        'Chinatown': 2,
        'Presidio': 3,
        'Fisherman\'s Wharf': 4
    }

    travel_times = [
        [0, 24, 30, 16, 29],    # Sunset District to others
        [23, 0, 9, 14, 7],      # Russian Hill to others
        [29, 7, 0, 19, 8],       # Chinatown to others
        [15, 14, 21, 0, 19],     # Presidio to others
        [27, 7, 12, 17, 0]       # Fisherman's Wharf to others
    ]

    # Define the friends and their availability
    friends = {
        'William': {'location': 'Russian Hill', 'start': 18.5, 'end': 20.75, 'min_duration': 105/60},
        'Michelle': {'location': 'Chinatown', 'start': 8.25, 'end': 14.0, 'min_duration': 15/60},
        'George': {'location': 'Presidio', 'start': 10.5, 'end': 18.75, 'min_duration': 30/60},
        'Robert': {'location': 'Fisherman\'s Wharf', 'start': 9.0, 'end': 13.75, 'min_duration': 30/60}
    }

    # Current location starts at Sunset District at 9:00 AM (9.0)
    current_time = Real('current_time')
    opt.add(current_time == 9.0)
    current_location = locations['Sunset District']

    # Variables for each meeting
    meetings = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        duration = Real(f'duration_{name}')
        meetings[name] = {'start': start, 'end': end, 'duration': duration}

    # Constraints for each meeting
    for name, data in friends.items():
        friend_loc = locations[data['location']]
        # Meeting must be within friend's availability
        opt.add(meetings[name]['start'] >= data['start'])
        opt.add(meetings[name]['end'] <= data['end'])
        # Meeting duration must be at least the minimum
        opt.add(meetings[name]['duration'] == meetings[name]['end'] - meetings[name]['start'])
        opt.add(meetings[name]['duration'] >= data['min_duration'])

    # Objective: maximize the total meeting time
    total_meeting_time = Real('total_meeting_time')
    opt.add(total_meeting_time == sum([meetings[name]['duration'] for name in friends]))
    opt.maximize(total_meeting_time)

    # Check if the optimizer can find a solution
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            start = m[meetings[name]['start']].as_fraction()
            end = m[meetings[name]['end']].as_fraction()
            start_time = float(start.numerator) / float(start.denominator)
            end_time = float(end.numerator) / float(end.denominator)
            # Convert to HH:MM format
            def to_hhmm(time):
                hours = int(time)
                minutes = int((time - hours) * 60)
                return f"{hours:02d}:{minutes:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": to_hhmm(start_time),
                "end_time": to_hhmm(end_time)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))