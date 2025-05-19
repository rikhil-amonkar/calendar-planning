import json
from itertools import permutations

# Travel times in minutes
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

# Friend availability
friends = {
    'Karen': {
        'location': 'Nob Hill',
        'start': 21.25,  # 9:15 PM
        'end': 21.75,    # 9:45 PM
        'duration': 0.5  # 30 minutes
    },
    'Joseph': {
        'location': 'Haight-Ashbury',
        'start': 12.5,   # 12:30 PM
        'end': 19.75,    # 7:45 PM
        'duration': 1.5  # 90 minutes
    },
    'Sandra': {
        'location': 'Chinatown',
        'start': 7.25,   # 7:15 AM
        'end': 19.25,    # 7:15 PM
        'duration': 1.25 # 75 minutes
    },
    'Nancy': {
        'location': 'Marina District',
        'start': 11.0,  # 11:00 AM
        'end': 20.25,    # 8:15 PM
        'duration': 1.75 # 105 minutes
    }
}

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(order):
    current_time = 9.0  # Start at Union Square at 9:00 AM
    current_location = 'Union Square'
    schedule = []
    met_friends = set()
    
    for friend in order:
        friend_data = friends[friend]
        location = friend_data['location']
        
        # Travel to friend's location
        travel_time = travel_times[current_location][location] / 60.0
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        meeting_start = max(arrival_time, friend_data['start'])
        meeting_end = meeting_start + friend_data['duration']
        
        if meeting_end > friend_data['end']:
            return None  # Can't meet this friend
        
        # Add meeting to schedule
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend,
            'start_time': float_to_time(meeting_start),
            'end_time': float_to_time(meeting_end)
        })
        
        met_friends.add(friend)
        current_time = meeting_end
        current_location = location
    
    # Check if we can meet Karen (she's only available late)
    if 'Karen' not in met_friends:
        friend_data = friends['Karen']
        location = friend_data['location']
        
        travel_time = travel_times[current_location][location] / 60.0
        arrival_time = current_time + travel_time
        
        meeting_start = max(arrival_time, friend_data['start'])
        meeting_end = meeting_start + friend_data['duration']
        
        if meeting_end <= friend_data['end']:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': 'Karen',
                'start_time': float_to_time(meeting_start),
                'end_time': float_to_time(meeting_end)
            })
            met_friends.add('Karen')
    
    return schedule if len(met_friends) == 4 else None

def find_optimal_schedule():
    best_schedule = None
    max_friends = 0
    
    # Try all possible orders of meeting the friends (except Karen who must be last)
    for order in permutations(['Joseph', 'Sandra', 'Nancy']):
        schedule = calculate_schedule(order)
        if schedule:
            if len(schedule) > max_friends:
                max_friends = len(schedule)
                best_schedule = schedule
            if max_friends == 4:
                break
    
    return best_schedule

def main():
    schedule = find_optimal_schedule()
    if not schedule:
        # Fallback if we can't meet all friends
        for order in permutations(['Joseph', 'Sandra', 'Nancy', 'Karen']):
            schedule = calculate_schedule(order)
            if schedule:
                break
    
    result = {
        "itinerary": schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()