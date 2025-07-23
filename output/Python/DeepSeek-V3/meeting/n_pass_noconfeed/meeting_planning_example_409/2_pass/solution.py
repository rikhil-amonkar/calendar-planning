import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters (same as before)
travel_times = {
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Golden Gate Park': 25,
        'Nob Hill': 11,
        'Marina District': 9,
        'Embarcadero': 8
    },
    'Bayview': {
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22,
        'Nob Hill': 20,
        'Marina District': 25,
        'Embarcadero': 19
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Nob Hill': 20,
        'Marina District': 16,
        'Embarcadero': 25
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'Bayview': 19,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Embarcadero': 9
    },
    'Marina District': {
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Golden Gate Park': 18,
        'Nob Hill': 12,
        'Embarcadero': 14
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Golden Gate Park': 25,
        'Nob Hill': 10,
        'Marina District': 12
    }
}

friends = [
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': '15:30',
        'available_end': '18:30',
        'min_duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Golden Gate Park',
        'available_start': '18:30',
        'available_end': '21:45',
        'min_duration': 30
    },
    {
        'name': 'Laura',
        'location': 'Nob Hill',
        'available_start': '8:45',
        'available_end': '16:15',
        'min_duration': 30
    },
    {
        'name': 'Betty',
        'location': 'Marina District',
        'available_start': '18:45',
        'available_end': '21:45',
        'min_duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Embarcadero',
        'available_start': '17:30',
        'available_end': '22:00',
        'min_duration': 45
    }
]

current_location = 'Fisherman\'s Wharf'
current_time = time_to_minutes('9:00')

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc]
    except KeyError:
        # Handle any potential typos in location names
        if 'Marina' in to_loc:
            return travel_times[from_loc]['Marina District']
        return travel_times[from_loc][to_loc]

def can_meet(friend, arrival_time):
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    min_duration = friend['min_duration']
    
    # Earliest we can start meeting is max of arrival time and friend's available start
    meeting_start = max(arrival_time, available_start)
    # Latest we can end is friend's available end
    meeting_end = available_end
    
    if meeting_end - meeting_start >= min_duration:
        # Try to meet for the minimum duration
        return (meeting_start, meeting_start + min_duration)
    return None

def generate_itinerary():
    itinerary = []
    remaining_friends = friends.copy()
    temp_location = current_location
    temp_time = current_time
    
    # Sort friends by earliest availability to try to meet them first
    remaining_friends.sort(key=lambda x: time_to_minutes(x['available_start']))
    
    while remaining_friends:
        best_friend = None
        best_meeting = None
        best_travel_time = float('inf')
        
        for friend in remaining_friends:
            location = friend['location']
            travel_time = get_travel_time(temp_location, location)
            arrival_time = temp_time + travel_time
            
            meeting = can_meet(friend, arrival_time)
            if meeting:
                # Prefer friends we can meet sooner
                if not best_meeting or meeting[0] < best_meeting[0]:
                    best_friend = friend
                    best_meeting = meeting
                    best_travel_time = travel_time
        
        if best_friend:
            meeting_start, meeting_end = best_meeting
            itinerary.append({
                'action': 'meet',
                'location': best_friend['location'],
                'person': best_friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end),
                'travel_time': best_travel_time
            })
            temp_location = best_friend['location']
            temp_time = meeting_end
            remaining_friends.remove(best_friend)
        else:
            break
    
    return itinerary

itinerary = generate_itinerary()
print(json.dumps({"itinerary": itinerary}, indent=2))