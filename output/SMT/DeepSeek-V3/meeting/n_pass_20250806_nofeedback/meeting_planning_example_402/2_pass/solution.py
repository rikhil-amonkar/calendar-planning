from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define the locations and their travel times
    locations = ['Golden Gate Park', 'Haight-Ashbury', 'Sunset District', 'Marina District', 'Financial District', 'Union Square']
    travel_times = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Union Square'): 30,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Union Square'): 16,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Sunset District'): 31,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Union Square'): 9,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Financial District'): 9,
    }

    # Define the friends and their availability
    friends = {
        'Sarah': {'location': 'Haight-Ashbury', 'start': 17*60, 'end': 21*60 + 30, 'duration': 105},
        'Patricia': {'location': 'Sunset District', 'start': 17*60, 'end': 19*60 + 45, 'duration': 45},
        'Matthew': {'location': 'Marina District', 'start': 9*60 + 15, 'end': 12*60, 'duration': 15},
        'Joseph': {'location': 'Financial District', 'start': 14*60 + 15, 'end': 18*60 + 45, 'duration': 30},
        'Robert': {'location': 'Union Square', 'start': 10*60 + 15, 'end': 21*60 + 45, 'duration': 15},
    }

    # Variables for meeting start times and durations
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}'),
        }

    # Current location and time
    current_location = 'Golden Gate Park'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each friend
    itinerary = []
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        start_available = friend['start']
        end_available = friend['end']
        duration = friend['duration']

        # Travel time to friend's location
        travel_time = travel_times[(current_location, loc)] if (current_location, loc) in travel_times else 0

        # Meeting must start after arrival and within friend's availability
        opt.add(Implies(meet_vars[name]['met'], meet_vars[name]['start'] >= start_available))
        opt.add(Implies(meet_vars[name]['met'], meet_vars[name]['start'] + duration <= end_available))
        opt.add(Implies(meet_vars[name]['met'], meet_vars[name]['start'] >= current_time + travel_time))

        # Update current time and location if meeting is scheduled
        current_time = If(meet_vars[name]['met'], meet_vars[name]['start'] + duration, current_time)
        current_location = If(meet_vars[name]['met'], loc, current_location)

        # Add to itinerary if meeting is scheduled
        itinerary.append({
            'action': 'meet',
            'person': name,
            'start_time': meet_vars[name]['start'],
            'end_time': meet_vars[name]['start'] + duration,
            'met': meet_vars[name]['met'],
        })

    # Maximize the number of friends met
    opt.maximize(Sum([If(meet_vars[name]['met'], 1, 0) for name in friends]))

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        result = []
        for entry in itinerary:
            if is_true(model.eval(entry['met'])):
                start = model.eval(entry['start_time']).as_long()
                end = model.eval(entry['end_time']).as_long()
                start_time = f"{start // 60:02d}:{start % 60:02d}"
                end_time = f"{end // 60:02d}:{end % 60:02d}"
                result.append({
                    "action": "meet",
                    "person": entry['person'],
                    "start_time": start_time,
                    "end_time": end_time,
                })
        return {"itinerary": result}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))