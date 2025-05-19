import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes between locations
travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'The Castro': 17,
        'Richmond District': 12,
        'Marina District': 21,
        'North Beach': 29,
        'Union Square': 30,
        'Golden Gate Park': 11
    },
    'Russian Hill': {
        'Sunset District': 23,
        'The Castro': 21,
        'Richmond District': 14,
        'Marina District': 7,
        'North Beach': 5,
        'Union Square': 11,
        'Golden Gate Park': 21
    },
    'The Castro': {
        'Sunset District': 17,
        'Russian Hill': 18,
        'Richmond District': 16,
        'Marina District': 21,
        'North Beach': 20,
        'Union Square': 19,
        'Golden Gate Park': 11
    },
    'Richmond District': {
        'Sunset District': 11,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'North Beach': 17,
        'Union Square': 21,
        'Golden Gate Park': 9
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18
    },
    'North Beach': {
        'Sunset District': 27,
        'Russian Hill': 4,
        'The Castro': 22,
        'Richmond District': 18,
        'Marina District': 9,
        'Union Square': 7,
        'Golden Gate Park': 22
    },
    'Union Square': {
        'Sunset District': 26,
        'Russian Hill': 13,
        'The Castro': 19,
        'Richmond District': 20,
        'Marina District': 18,
        'North Beach': 10,
        'Golden Gate Park': 22
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Russian Hill': 19,
        'The Castro': 13,
        'Richmond District': 7,
        'Marina District': 16,
        'North Beach': 24,
        'Union Square': 22
    }
}

# Correcting some typos in the travel_times keys
travel_times['Russian Hill']['Richmond District'] = 14
travel_times['Marina District'] = travel_times.pop('Marina District')
travel_times['Richmond District'] = travel_times.pop('Richmond District')

# Friend constraints
friends = [
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': '20:45',
        'available_end': '21:45',
        'min_duration': 60
    },
    {
        'name': 'Jessica',
        'location': 'The Castro',
        'available_start': '15:45',
        'available_end': '19:30',
        'min_duration': 60
    },
    {
        'name': 'Matthew',
        'location': 'Richmond District',
        'available_start': '7:30',
        'available_end': '15:15',
        'min_duration': 15
    },
    {
        'name': 'Michelle',
        'location': 'Marina District',
        'available_start': '10:30',
        'available_end': '18:45',
        'min_duration': 75
    },
    {
        'name': 'Carol',
        'location': 'North Beach',
        'available_start': '12:00',
        'available_end': '17:00',
        'min_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'available_start': '10:45',
        'available_end': '14:15',
        'min_duration': 30
    },
    {
        'name': 'Linda',
        'location': 'Golden Gate Park',
        'available_start': '10:45',
        'available_end': '22:00',
        'min_duration': 90
    }
]

def calculate_schedule():
    current_time = time_to_minutes('9:00')
    current_location = 'Sunset District'
    itinerary = []
    met_friends = set()
    
    # We'll try to meet friends in different orders to find the best schedule
    friend_permutations = permutations([f for f in friends if f['name'] not in ['Karen']])  # Karen is only available late
    
    best_itinerary = []
    max_meetings = 0
    
    for perm in friend_permutations:
        temp_itinerary = []
        temp_current_time = current_time
        temp_current_location = current_location
        temp_met_friends = set()
        temp_perm = list(perm) + [friends[0]]  # Add Karen last
        
        for friend in temp_perm:
            if friend['name'] in temp_met_friends:
                continue
                
            # Calculate travel time
            travel_time = travel_times[temp_current_location].get(friend['location'], float('inf'))
            arrival_time = temp_current_time + travel_time
            
            # Check if we can meet this friend
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            min_duration = friend['min_duration']
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + min_duration
            
            if meeting_end > available_end:
                continue  # Can't meet this friend
                
            # Add to itinerary
            temp_itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            temp_met_friends.add(friend['name'])
            temp_current_time = meeting_end
            temp_current_location = friend['location']
        
        # Check if this permutation is better
        if len(temp_met_friends) > max_meetings or (len(temp_met_friends) == max_meetings and temp_current_time < time_to_minutes('22:00')):
            max_meetings = len(temp_met_friends)
            best_itinerary = temp_itinerary
    
    # Try to meet Karen if possible
    karen = friends[0]
    travel_time = travel_times[best_itinerary[-1]['location'] if best_itinerary else travel_times[current_location]
    travel_time = travel_time.get(karen['location'], float('inf'))
    arrival_time = time_to_minutes(best_itinerary[-1]['end_time']) if best_itinerary else current_time
    arrival_time += travel_time
    
    available_start = time_to_minutes(karen['available_start'])
    available_end = time_to_minutes(karen['available_end'])
    min_duration = karen['min_duration']
    
    meeting_start = max(arrival_time, available_start)
    meeting_end = meeting_start + min_duration
    
    if meeting_end <= available_end:
        best_itinerary.append({
            'action': 'meet',
            'location': karen['location'],
            'person': karen['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
    
    return best_itinerary

def main():
    itinerary = calculate_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()