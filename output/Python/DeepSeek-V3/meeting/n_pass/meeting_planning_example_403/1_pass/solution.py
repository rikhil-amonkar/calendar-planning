import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    'Union Square': {
        'Golden Gate Park': 22,
        'Pacific Heights': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'The Castro': 19
    },
    'Golden Gate Park': {
        'Union Square': 22,
        'Pacific Heights': 16,
        'Presidio': 11,
        'Chinatown': 23,
        'The Castro': 13
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Presidio': 11,
        'Chinatown': 11,
        'The Castro': 16
    },
    'Presidio': {
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Pacific Heights': 11,
        'Chinatown': 21,
        'The Castro': 21
    },
    'Chinatown': {
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Pacific Heights': 10,
        'Presidio': 19,
        'The Castro': 22
    },
    'The Castro': {
        'Union Square': 19,
        'Golden Gate Park': 11,
        'Pacific Heights': 16,
        'Presidio': 20,
        'Chinatown': 20
    }
}

# Friend constraints
friends = [
    {
        'name': 'Andrew',
        'location': 'Golden Gate Park',
        'start': '11:45',
        'end': '14:30',
        'min_duration': 75
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'start': '16:15',
        'end': '18:45',
        'min_duration': 15
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'start': '17:30',
        'end': '19:15',
        'min_duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Chinatown',
        'start': '9:45',
        'end': '21:30',
        'min_duration': 90
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'start': '8:30',
        'end': '14:15',
        'min_duration': 30
    }
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = next(f for f in friends if f['name'] == friend_name)
        location = friend['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        start_window = time_to_minutes(friend['start'])
        end_window = time_to_minutes(friend['end'])
        min_duration = friend['min_duration']
        
        # Calculate possible meeting start time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > end_window:
            return None  # Cannot meet this friend
        
        schedule.append({
            'action': 'travel',
            'location': location,
            'start_time': minutes_to_time(current_time),
            'end_time': minutes_to_time(arrival_time)
        })
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        met_friends.add(friend['name'])
        current_time = meeting_end
        current_location = location
    
    return {
        'itinerary': schedule,
        'met_friends': met_friends
    }

def find_optimal_schedule():
    friend_names = [f['name'] for f in friends]
    best_schedule = None
    max_met = 0
    
    # Try all possible orders of meeting friends
    for order in permutations(friend_names):
        schedule = calculate_schedule(order)
        if schedule and len(schedule['met_friends']) > max_met:
            max_met = len(schedule['met_friends'])
            best_schedule = schedule
        elif schedule and len(schedule['met_friends']) == max_met:
            # Prefer schedules that meet more important friends first
            pass
    
    return best_schedule

optimal_schedule = find_optimal_schedule()
if optimal_schedule:
    print(json.dumps(optimal_schedule['itinerary'], indent=2))
else:
    print(json.dumps({"error": "No valid schedule found"}, indent=2))