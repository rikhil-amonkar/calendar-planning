import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times dictionary: {from: {to: minutes}}
    travel_times = {
        'Union Square': {
            'The Castro': 17, 'North Beach': 10, 'Embarcadero': 11, 'Alamo Square': 15,
            'Nob Hill': 9, 'Presidio': 24, 'Fisherman\'s Wharf': 15, 'Mission District': 14,
            'Haight-Ashbury': 18
        },
        'The Castro': {
            'Union Square': 19, 'North Beach': 20, 'Embarcadero': 22, 'Alamo Square': 8,
            'Nob Hill': 16, 'Presidio': 20, 'Fisherman\'s Wharf': 24, 'Mission District': 7,
            'Haight-Ashbury': 6
        },
        'North Beach': {
            'Union Square': 7, 'The Castro': 23, 'Embarcadero': 6, 'Alamo Square': 16,
            'Nob Hill': 7, 'Presidio': 17, 'Fisherman\'s Wharf': 5, 'Mission District': 18,
            'Haight-Ashbury': 18
        },
        'Embarcadero': {
            'Union Square': 10, 'The Castro': 25, 'North Beach': 5, 'Alamo Square': 19,
            'Nob Hill': 10, 'Presidio': 20, 'Fisherman\'s Wharf': 6, 'Mission District': 20,
            'Haight-Ashbury': 21
        },
        'Alamo Square': {
            'Union Square': 14, 'The Castro': 8, 'North Beach': 15, 'Embarcadero': 16,
            'Nob Hill': 11, 'Presidio': 17, 'Fisherman\'s Wharf': 19, 'Mission District': 10,
            'Haight-Ashbury': 5
        },
        'Nob Hill': {
            'Union Square': 7, 'The Castro': 17, 'North Beach': 8, 'Embarcadero': 9,
            'Alamo Square': 11, 'Presidio': 17, 'Fisherman\'s Wharf': 10, 'Mission District': 13,
            'Haight-Ashbury': 13
        },
        'Presidio': {
            'Union Square': 22, 'The Castro': 21, 'North Beach': 18, 'Embarcadero': 20,
            'Alamo Square': 19, 'Nob Hill': 18, 'Fisherman\'s Wharf': 19, 'Mission District': 26,
            'Haight-Ashbury': 15
        },
        'Fisherman\'s Wharf': {
            'Union Square': 13, 'The Castro': 27, 'North Beach': 6, 'Embarcadero': 8,
            'Alamo Square': 21, 'Nob Hill': 11, 'Presidio': 17, 'Mission District': 22,
            'Haight-Ashbury': 22
        },
        'Mission District': {
            'Union Square': 15, 'The Castro': 7, 'North Beach': 17, 'Embarcadero': 19,
            'Alamo Square': 11, 'Nob Hill': 12, 'Presidio': 25, 'Fisherman\'s Wharf': 22,
            'Haight-Ashbury': 12
        },
        'Haight-Ashbury': {
            'Union Square': 19, 'The Castro': 6, 'North Beach': 19, 'Embarcadero': 20,
            'Alamo Square': 5, 'Nob Hill': 15, 'Presidio': 15, 'Fisherman\'s Wharf': 23,
            'Mission District': 11
        }
    }

    # Friend constraints
    friends = [
        {'name': 'Melissa', 'location': 'The Castro', 'start': '20:15', 'end': '21:15', 'duration': 30},
        {'name': 'Kimberly', 'location': 'North Beach', 'start': '7:00', 'end': '10:30', 'duration': 15},
        {'name': 'Joseph', 'location': 'Embarcadero', 'start': '15:30', 'end': '19:30', 'duration': 75},
        {'name': 'Barbara', 'location': 'Alamo Square', 'start': '20:45', 'end': '21:45', 'duration': 15},
        {'name': 'Kenneth', 'location': 'Nob Hill', 'start': '12:15', 'end': '17:15', 'duration': 105},
        {'name': 'Joshua', 'location': 'Presidio', 'start': '16:30', 'end': '18:15', 'duration': 105},
        {'name': 'Brian', 'location': 'Fisherman\'s Wharf', 'start': '9:30', 'end': '15:30', 'duration': 45},
        {'name': 'Steven', 'location': 'Mission District', 'start': '19:30', 'end': '21:00', 'duration': 90},
        {'name': 'Betty', 'location': 'Haight-Ashbury', 'start': '19:00', 'end': '20:30', 'duration': 90}
    ]

    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    itinerary = []
    met_friends = set()

    # Helper function to find next possible friend to meet
    def find_next_friend(current_loc, current_t, met):
        best_friend = None
        best_start = None
        best_end = None
        best_travel = float('inf')
        
        for friend in friends:
            if friend['name'] in met:
                continue
                
            loc = friend['location']
            travel_time = travel_times[current_loc][loc]
            available_start = time_to_minutes(friend['start'])
            available_end = time_to_minutes(friend['end'])
            
            # Earliest we can arrive
            arrival_time = current_t + travel_time
            if arrival_time > available_end:
                continue
                
            # Calculate meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = min(meeting_start + friend['duration'], available_end)
            
            if meeting_end - meeting_start >= friend['duration']:
                if travel_time < best_travel:
                    best_friend = friend
                    best_start = meeting_start
                    best_end = meeting_end
                    best_travel = travel_time
        
        return best_friend, best_start, best_end, best_travel

    # Greedy algorithm to meet as many friends as possible
    while True:
        next_friend, start, end, travel = find_next_friend(current_location, current_time, met_friends)
        if not next_friend:
            break
            
        itinerary.append({
            'action': 'meet',
            'location': next_friend['location'],
            'person': next_friend['name'],
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end)
        })
        
        met_friends.add(next_friend['name'])
        current_time = end
        current_location = next_friend['location']

    return {'itinerary': itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))