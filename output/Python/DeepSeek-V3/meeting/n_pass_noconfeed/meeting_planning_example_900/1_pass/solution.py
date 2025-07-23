import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary
travel_times = {
    'Richmond District': {
        'The Castro': 16, 'Nob Hill': 17, 'Marina District': 9, 'Pacific Heights': 10,
        'Haight-Ashbury': 10, 'Mission District': 20, 'Chinatown': 20, 'Russian Hill': 13,
        'Alamo Square': 13, 'Bayview': 27
    },
    'The Castro': {
        'Richmond District': 16, 'Nob Hill': 16, 'Marina District': 21, 'Pacific Heights': 16,
        'Haight-Ashbury': 6, 'Mission District': 7, 'Chinatown': 22, 'Russian Hill': 18,
        'Alamo Square': 8, 'Bayview': 19
    },
    'Nob Hill': {
        'Richmond District': 14, 'The Castro': 17, 'Marina District': 11, 'Pacific Heights': 8,
        'Haight-Ashbury': 13, 'Mission District': 13, 'Chinatown': 6, 'Russian Hill': 5,
        'Alamo Square': 11, 'Bayview': 19
    },
    'Marina District': {
        'Richmond District': 11, 'The Castro': 22, 'Nob Hill': 12, 'Pacific Heights': 7,
        'Haight-Ashbury': 16, 'Mission District': 20, 'Chinatown': 15, 'Russian Hill': 8,
        'Alamo Square': 15, 'Bayview': 27
    },
    'Pacific Heights': {
        'Richmond District': 12, 'The Castro': 16, 'Nob Hill': 8, 'Marina District': 6,
        'Haight-Ashbury': 11, 'Mission District': 15, 'Chinatown': 11, 'Russian Hill': 7,
        'Alamo Square': 10, 'Bayview': 22
    },
    'Haight-Ashbury': {
        'Richmond District': 10, 'The Castro': 6, 'Nob Hill': 15, 'Marina District': 17,
        'Pacific Heights': 12, 'Mission District': 11, 'Chinatown': 19, 'Russian Hill': 17,
        'Alamo Square': 5, 'Bayview': 18
    },
    'Mission District': {
        'Richmond District': 20, 'The Castro': 7, 'Nob Hill': 12, 'Marina District': 19,
        'Pacific Heights': 16, 'Haight-Ashbury': 12, 'Chinatown': 16, 'Russian Hill': 15,
        'Alamo Square': 11, 'Bayview': 14
    },
    'Chinatown': {
        'Richmond District': 20, 'The Castro': 22, 'Nob Hill': 9, 'Marina District': 12,
        'Pacific Heights': 10, 'Haight-Ashbury': 19, 'Mission District': 17, 'Russian Hill': 7,
        'Alamo Square': 17, 'Bayview': 20
    },
    'Russian Hill': {
        'Richmond District': 14, 'The Castro': 21, 'Nob Hill': 5, 'Marina District': 7,
        'Pacific Heights': 7, 'Haight-Ashbury': 17, 'Mission District': 16, 'Chinatown': 9,
        'Alamo Square': 15, 'Bayview': 23
    },
    'Alamo Square': {
        'Richmond District': 11, 'The Castro': 8, 'Nob Hill': 11, 'Marina District': 15,
        'Pacific Heights': 10, 'Haight-Ashbury': 5, 'Mission District': 10, 'Chinatown': 15,
        'Russian Hill': 13, 'Bayview': 16
    },
    'Bayview': {
        'Richmond District': 25, 'The Castro': 19, 'Nob Hill': 20, 'Marina District': 27,
        'Pacific Heights': 23, 'Haight-Ashbury': 19, 'Mission District': 13, 'Chinatown': 19,
        'Russian Hill': 23, 'Alamo Square': 16
    }
}

# Friends' availability
friends = [
    {'name': 'Matthew', 'location': 'The Castro', 'start': '16:30', 'end': '20:00', 'duration': 45},
    {'name': 'Rebecca', 'location': 'Nob Hill', 'start': '15:15', 'end': '19:15', 'duration': 105},
    {'name': 'Brian', 'location': 'Marina District', 'start': '14:15', 'end': '22:00', 'duration': 30},
    {'name': 'Emily', 'location': 'Pacific Heights', 'start': '11:15', 'end': '19:45', 'duration': 15},
    {'name': 'Karen', 'location': 'Haight-Ashbury', 'start': '11:45', 'end': '17:30', 'duration': 30},
    {'name': 'Stephanie', 'location': 'Mission District', 'start': '13:00', 'end': '15:45', 'duration': 75},
    {'name': 'James', 'location': 'Chinatown', 'start': '14:30', 'end': '19:00', 'duration': 120},
    {'name': 'Steven', 'location': 'Russian Hill', 'start': '14:00', 'end': '20:00', 'duration': 30},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': '13:00', 'end': '17:15', 'duration': 120},
    {'name': 'William', 'location': 'Bayview', 'start': '18:15', 'end': '20:15', 'duration': 90}
]

def calculate_schedule():
    current_location = 'Richmond District'
    current_time = time_to_minutes('9:00')
    itinerary = []
    remaining_friends = friends.copy()
    
    # Prioritize friends with tightest windows first
    remaining_friends.sort(key=lambda x: (time_to_minutes(x['end']) - time_to_minutes(x['start'])))
    
    while remaining_friends:
        best_friend = None
        best_start = None
        best_end = None
        best_travel = float('inf')
        
        for friend in remaining_friends:
            travel_time = travel_times[current_location][friend['location']]
            friend_start = time_to_minutes(friend['start'])
            friend_end = time_to_minutes(friend['end'])
            
            # Earliest we can arrive
            arrival_time = current_time + travel_time
            earliest_start = max(arrival_time, friend_start)
            earliest_end = earliest_start + friend['duration']
            
            if earliest_end <= friend_end:
                if best_friend is None or earliest_start < best_start:
                    best_friend = friend
                    best_start = earliest_start
                    best_end = earliest_end
                    best_travel = travel_time
        
        if best_friend is None:
            break
            
        itinerary.append({
            'action': 'meet',
            'location': best_friend['location'],
            'person': best_friend['name'],
            'start_time': minutes_to_time(best_start),
            'end_time': minutes_to_time(best_end)
        })
        
        current_location = best_friend['location']
        current_time = best_end
        remaining_friends.remove(best_friend)
    
    return itinerary

def main():
    itinerary = calculate_schedule()
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()