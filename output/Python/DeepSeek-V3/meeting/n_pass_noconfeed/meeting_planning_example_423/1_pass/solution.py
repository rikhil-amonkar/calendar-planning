import json
from itertools import permutations

# Travel times in minutes between locations
travel_times = {
    'Presidio': {
        'Richmond District': 7,
        'North Beach': 18,
        'Financial District': 23,
        'Golden Gate Park': 12,
        'Union Square': 22
    },
    'Richmond District': {
        'Presidio': 7,
        'North Beach': 17,
        'Financial District': 22,
        'Golden Gate Park': 9,
        'Union Square': 21
    },
    'North Beach': {
        'Presidio': 17,
        'Richmond District': 18,
        'Financial District': 8,
        'Golden Gate Park': 22,
        'Union Square': 7
    },
    'Financial District': {
        'Presidio': 22,
        'Richmond District': 21,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Union Square': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Richmond District': 7,
        'North Beach': 24,
        'Financial District': 26,
        'Union Square': 22
    },
    'Union Square': {
        'Presidio': 24,
        'Richmond District': 20,
        'North Beach': 10,
        'Financial District': 9,
        'Golden Gate Park': 22
    }
}

# Meeting constraints
friends = {
    'Jason': {
        'location': 'Richmond District',
        'available_start': '13:00',
        'available_end': '20:45',
        'min_duration': 90
    },
    'Melissa': {
        'location': 'North Beach',
        'available_start': '18:45',
        'available_end': '20:15',
        'min_duration': 45
    },
    'Brian': {
        'location': 'Financial District',
        'available_start': '9:45',
        'available_end': '21:45',
        'min_duration': 15
    },
    'Elizabeth': {
        'location': 'Golden Gate Park',
        'available_start': '8:45',
        'available_end': '21:30',
        'min_duration': 105
    },
    'Laura': {
        'location': 'Union Square',
        'available_start': '14:15',
        'available_end': '19:30',
        'min_duration': 75
    }
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule(order):
    current_location = 'Presidio'
    current_time = time_to_minutes('9:00')
    schedule = []
    met_friends = set()
    
    for friend in order:
        friend_data = friends[friend]
        location = friend_data['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(friend_data['available_start'])
        available_end = time_to_minutes(friend_data['available_end'])
        min_duration = friend_data['min_duration']
        
        # Calculate meeting window
        start_time = max(arrival_time, available_start)
        end_time = min(start_time + min_duration, available_end)
        
        if end_time > start_time and end_time <= available_end:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': friend,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            met_friends.add(friend)
            current_time = end_time
            current_location = location
        else:
            return None, set()
    
    return schedule, met_friends

def find_optimal_schedule():
    best_schedule = []
    max_met = 0
    
    # Try all possible permutations of friends
    for order in permutations(friends.keys()):
        schedule, met_friends = calculate_schedule(order)
        if len(met_friends) > max_met:
            max_met = len(met_friends)
            best_schedule = schedule
        elif len(met_friends) == max_met and schedule:
            # Prefer schedules that meet more important friends or have other criteria
            pass
    
    return best_schedule

# Find the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output the result as JSON
output = {
    "itinerary": optimal_schedule
}
print(json.dumps(output, indent=2))