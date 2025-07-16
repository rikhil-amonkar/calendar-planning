import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Bayview': {
        'Nob Hill': 20,
        'Union Square': 17,
        'Chinatown': 18,
        'The Castro': 20,
        'Presidio': 31,
        'Pacific Heights': 23,
        'Russian Hill': 23
    },
    'Nob Hill': {
        'Bayview': 19,
        'Union Square': 7,
        'Chinatown': 6,
        'The Castro': 17,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Russian Hill': 5
    },
    'Union Square': {
        'Bayview': 15,
        'Nob Hill': 9,
        'Chinatown': 7,
        'The Castro': 19,
        'Presidio': 24,
        'Pacific Heights': 15,
        'Russian Hill': 13
    },
    'Chinatown': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 7,
        'The Castro': 22,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Russian Hill': 7
    },
    'The Castro': {
        'Bayview': 19,
        'Nob Hill': 16,
        'Union Square': 19,
        'Chinatown': 20,
        'Presidio': 20,
        'Pacific Heights': 16,
        'Russian Hill': 18
    },
    'Presidio': {
        'Bayview': 31,
        'Nob Hill': 18,
        'Union Square': 22,
        'Chinatown': 21,
        'The Castro': 21,
        'Pacific Heights': 11,
        'Russian Hill': 14
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 12,
        'Chinatown': 11,
        'The Castro': 16,
        'Presidio': 11,
        'Russian Hill': 7
    },
    'Russian Hill': {
        'Bayview': 23,
        'Nob Hill': 5,
        'Union Square': 11,
        'Chinatown': 9,
        'The Castro': 21,
        'Presidio': 14,
        'Pacific Heights': 7
    }
}

# Friend availability
friends = {
    'Paul': {
        'location': 'Nob Hill',
        'start': 16.25,  # 4:15 PM
        'end': 21.25,    # 9:15 PM
        'duration': 60   # minutes
    },
    'Carol': {
        'location': 'Union Square',
        'start': 18.0,   # 6:00 PM
        'end': 20.25,    # 8:15 PM
        'duration': 120  # minutes
    },
    'Patricia': {
        'location': 'Chinatown',
        'start': 20.0,  # 8:00 PM
        'end': 21.5,     # 9:30 PM
        'duration': 75  # minutes
    },
    'Karen': {
        'location': 'The Castro',
        'start': 17.0,   # 5:00 PM
        'end': 19.0,     # 7:00 PM
        'duration': 45   # minutes
    },
    'Nancy': {
        'location': 'Presidio',
        'start': 11.75, # 11:45 AM
        'end': 22.0,     # 10:00 PM
        'duration': 30   # minutes
    },
    'Jeffrey': {
        'location': 'Pacific Heights',
        'start': 20.0,   # 8:00 PM
        'end': 20.75,    # 8:45 PM
        'duration': 45   # minutes
    },
    'Matthew': {
        'location': 'Russian Hill',
        'start': 15.75,  # 3:45 PM
        'end': 21.75,    # 9:45 PM
        'duration': 75    # minutes
    }
}

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc] / 60.0  # Convert to hours

def can_meet_friend(current_time, friend_name, current_location):
    friend = friends[friend_name]
    travel_time = get_travel_time(current_location, friend['location'])
    arrival_time = current_time + travel_time
    
    # Calculate possible meeting window
    meeting_start = max(arrival_time, friend['start'])
    meeting_end = min(meeting_start + friend['duration'] / 60.0, friend['end'])
    
    if meeting_end - meeting_start >= friend['duration'] / 60.0:
        return True, meeting_start, meeting_end
    return False, None, None

def evaluate_schedule(schedule):
    current_time = 9.0  # Start at Bayview at 9:00 AM
    current_location = 'Bayview'
    itinerary = []
    met_friends = set()
    
    for friend_name in schedule:
        if friend_name in met_friends:
            continue
            
        can_meet, start, end = can_meet_friend(current_time, friend_name, current_location)
        if can_meet:
            itinerary.append({
                'action': 'meet',
                'location': friends[friend_name]['location'],
                'person': friend_name,
                'start_time': float_to_time(start),
                'end_time': float_to_time(end)
            })
            met_friends.add(friend_name)
            current_time = end
            current_location = friends[friend_name]['location']
    
    return len(met_friends), itinerary

def generate_best_schedule():
    friend_names = list(friends.keys())
    best_count = 0
    best_itinerary = []
    
    # Try all permutations of friends (limited to 5 friends for performance)
    for perm in permutations(friend_names, min(5, len(friend_names))):
        count, itinerary = evaluate_schedule(perm)
        if count > best_count:
            best_count = count
            best_itinerary = itinerary
    
    return best_itinerary

def main():
    best_itinerary = generate_best_schedule()
    result = {
        'itinerary': best_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()