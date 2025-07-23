import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
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
        return travel_times[from_loc][to_loc.replace('Marina District', 'Marina District')]

def can_meet(friend, start_time, end_time):
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    min_duration = friend['min_duration']
    
    meeting_start = max(start_time, available_start)
    meeting_end = min(end_time, available_end)
    
    if meeting_end - meeting_start >= min_duration:
        return (meeting_start, meeting_end)
    return None

def evaluate_schedule(order):
    global current_location, current_time
    itinerary = []
    temp_location = current_location
    temp_time = current_time
    
    for friend in order:
        location = friend['location']
        travel_time = get_travel_time(temp_location, location)
        arrival_time = temp_time + travel_time
        
        meeting = can_meet(friend, arrival_time, time_to_minutes(friend['available_end']))
        if not meeting:
            return None
        
        meeting_start, meeting_end = meeting
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        temp_location = location
        temp_time = meeting_end
    
    return itinerary

best_itinerary = None
max_meetings = 0

# Try all permutations of friends to find the best schedule
for perm in permutations(friends):
    itinerary = evaluate_schedule(perm)
    if itinerary and len(itinerary) > max_meetings:
        best_itinerary = itinerary
        max_meetings = len(itinerary)
    elif itinerary and len(itinerary) == max_meetings:
        # Prefer longer total meeting time
        current_duration = sum(time_to_minutes(item['end_time']) - time_to_minutes(item['start_time']) for item in itinerary)
        best_duration = sum(time_to_minutes(item['end_time']) - time_to_minutes(item['start_time']) for item in best_itinerary)
        if current_duration > best_duration:
            best_itinerary = itinerary

# Output the result
if best_itinerary:
    print(json.dumps({"itinerary": best_itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))