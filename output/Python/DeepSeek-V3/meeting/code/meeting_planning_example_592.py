import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'North Beach': {
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Mission District': 18,
        'Golden Gate Park': 22,
        'Nob Hill': 7
    },
    'Pacific Heights': {
        'North Beach': 9,
        'Chinatown': 11,
        'Union Square': 12,
        'Mission District': 15,
        'Golden Gate Park': 15,
        'Nob Hill': 8
    },
    'Chinatown': {
        'North Beach': 3,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Mission District': 18,
        'Golden Gate Park': 23,
        'Nob Hill': 8
    },
    'Union Square': {
        'North Beach': 10,
        'Pacific Heights': 15,
        'Chinatown': 7,
        'Mission District': 14,
        'Golden Gate Park': 22,
        'Nob Hill': 9
    },
    'Mission District': {
        'North Beach': 17,
        'Pacific Heights': 16,
        'Chinatown': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Nob Hill': 12
    },
    'Golden Gate Park': {
        'North Beach': 24,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Union Square': 22,
        'Mission District': 17,
        'Nob Hill': 20
    },
    'Nob Hill': {
        'North Beach': 8,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Mission District': 13,
        'Golden Gate Park': 17
    }
}

# Friend availability and constraints
friends = {
    'James': {
        'location': 'Pacific Heights',
        'start': '20:00',
        'end': '22:00',
        'min_duration': 120
    },
    'Robert': {
        'location': 'Chinatown',
        'start': '12:15',
        'end': '16:45',
        'min_duration': 90
    },
    'Jeffrey': {
        'location': 'Union Square',
        'start': '9:30',
        'end': '15:30',
        'min_duration': 120
    },
    'Carol': {
        'location': 'Mission District',
        'start': '18:15',
        'end': '21:15',
        'min_duration': 15
    },
    'Mark': {
        'location': 'Golden Gate Park',
        'start': '11:30',
        'end': '17:45',
        'min_duration': 15
    },
    'Sandra': {
        'location': 'Nob Hill',
        'start': '8:00',
        'end': '15:30',
        'min_duration': 15
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
    current_location = 'North Beach'
    current_time = time_to_minutes('9:00')
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = friends[friend_name]
        location = friend['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        start_window = time_to_minutes(friend['start'])
        end_window = time_to_minutes(friend['end'])
        min_duration = friend['min_duration']
        
        # Calculate possible meeting time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > end_window:
            return None  # Can't meet this friend
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend_name,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        met_friends.add(friend_name)
        current_location = location
        current_time = meeting_end
    
    # Check if we can meet James (special case since it's late)
    if 'James' not in met_friends:
        friend = friends['James']
        location = friend['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        start_window = time_to_minutes(friend['start'])
        end_window = time_to_minutes(friend['end'])
        min_duration = friend['min_duration']
        
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + min_duration
        
        if meeting_end <= end_window:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': 'James',
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            met_friends.add('James')
    
    return schedule if len(met_friends) == len(friends) else None

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    # Prioritize meeting all friends, then minimize travel time
    return len(schedule) * 1000 - sum(travel_times[schedule[i]['location']][schedule[i+1]['location']] 
                                     for i in range(len(schedule)-1) if i+1 < len(schedule))

def find_optimal_schedule():
    best_score = -1
    best_schedule = None
    friend_names = [name for name in friends if name != 'James']
    
    # Try different permutations of friends (except James who is handled specially)
    for perm in permutations(friend_names):
        # Try with James at the end
        order = list(perm) + ['James']
        schedule = calculate_schedule(order)
        score = evaluate_schedule(schedule)
        if score > best_score:
            best_score = score
            best_schedule = schedule
        
        # Try without James (if we can meet him during the day)
        order = list(perm)
        schedule = calculate_schedule(order)
        score = evaluate_schedule(schedule)
        if score > best_score:
            best_score = score
            best_schedule = schedule
    
    return best_schedule

optimal_schedule = find_optimal_schedule()
result = {"itinerary": optimal_schedule} if optimal_schedule else {"itinerary": []}
print(json.dumps(result, indent=2))