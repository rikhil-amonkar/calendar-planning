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
    'Bayview': {'North Beach': 21, 'Presidio': 31, 'Haight-Ashbury': 19, 'Union Square': 17},
    'North Beach': {'Bayview': 22, 'Presidio': 17, 'Haight-Ashbury': 18, 'Union Square': 7},
    'Presidio': {'Bayview': 31, 'North Beach': 18, 'Haight-Ashbury': 15, 'Union Square': 22},
    'Haight-Ashbury': {'Bayview': 18, 'North Beach': 19, 'Presidio': 15, 'Union Square': 17},
    'Union Square': {'Bayview': 15, 'North Beach': 10, 'Presidio': 24, 'Haight-Ashbury': 18}
}

friends = [
    {'name': 'Barbara', 'location': 'North Beach', 'start': '13:45', 'end': '20:15', 'duration': 60},
    {'name': 'Margaret', 'location': 'Presidio', 'start': '10:15', 'end': '15:15', 'duration': 30},
    {'name': 'Kevin', 'location': 'Haight-Ashbury', 'start': '20:00', 'end': '20:45', 'duration': 30},
    {'name': 'Kimberly', 'location': 'Union Square', 'start': '7:45', 'end': '16:45', 'duration': 30}
]

current_location = 'Bayview'
current_time = time_to_minutes('9:00')

def generate_schedules():
    schedules = []
    for perm in permutations(friends):
        schedules.append(list(perm))
    return schedules

def is_meeting_possible(schedule, current_location, current_time):
    itinerary = []
    temp_location = current_location
    temp_time = current_time
    
    for friend in schedule:
        # Travel to friend's location
        travel_time = travel_times[temp_location][friend['location']]
        arrival_time = temp_time + travel_time
        
        # Check if arrival is within friend's window
        friend_start = time_to_minutes(friend['start'])
        friend_end = time_to_minutes(friend['end'])
        
        if arrival_time > friend_end:
            return None  # Can't meet
        
        meeting_start = max(arrival_time, friend_start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend_end:
            return None  # Can't meet for required duration
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        temp_location = friend['location']
        temp_time = meeting_end
    
    return itinerary

def find_best_schedule():
    schedules = generate_schedules()
    best_itinerary = None
    max_meetings = 0
    
    for schedule in schedules:
        itinerary = is_meeting_possible(schedule, current_location, current_time)
        if itinerary and len(itinerary) > max_meetings:
            max_meetings = len(itinerary)
            best_itinerary = itinerary
    
    return best_itinerary

best_schedule = find_best_schedule()

if best_schedule:
    output = {'itinerary': best_schedule}
else:
    output = {'itinerary': []}

print(json.dumps(output, indent=2))