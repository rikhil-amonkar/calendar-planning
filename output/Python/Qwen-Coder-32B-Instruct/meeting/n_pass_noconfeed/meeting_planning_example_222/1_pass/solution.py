import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Bayview'): 22,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Fisherman\'s Wharf'): 25
}

# Define meeting constraints
meetings = {
    'Helen': {'location': 'North Beach', 'available': (datetime.strptime('7:00', '%H:%M'), datetime.strptime('16:45', '%H:%M')), 'min_duration': 120},
    'Kimberly': {'location': 'Fisherman\'s Wharf', 'available': (datetime.strptime('16:30', '%H:%M'), datetime.strptime('21:00', '%H:%M')), 'min_duration': 45},
    'Patricia': {'location': 'Bayview', 'available': (datetime.strptime('18:00', '%H:%M'), datetime.strptime('21:15', '%H:%M')), 'min_duration': 120}
}

# Start time
start_time = datetime.strptime('9:00', '%H:%M')

def format_time(time):
    return time.strftime('%H:%M').lstrip('0')

def find_schedule(start_time, current_location, meetings_left, itinerary, current_time):
    if not meetings_left:
        return itinerary
    
    best_itinerary = None
    
    for person, details in meetings_left.items():
        location = details['location']
        available_start, available_end = details['available']
        min_duration = details['min_duration']
        
        # Calculate travel time
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we can meet the person within their availability
        if arrival_time < available_start:
            arrival_time = available_start
        
        meeting_start_time = arrival_time
        meeting_end_time = meeting_start_time + timedelta(minutes=min_duration)
        
        if meeting_end_time <= available_end:
            new_itinerary = itinerary + [{
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(meeting_start_time),
                "end_time": format_time(meeting_end_time)
            }]
            
            remaining_meetings = {k: v for k, v in meetings_left.items() if k != person}
            result_itinerary = find_schedule(start_time, location, remaining_meetings, new_itinerary, meeting_end_time)
            
            if result_itinerary is not None:
                if best_itinerary is None or len(result_itinerary) > len(best_itinerary):
                    best_itinerary = result_itinerary
    
    return best_itinerary

# Find the optimal itinerary
optimal_itinerary = find_schedule(start_time, 'Nob Hill', meetings, [], start_time)

# Output the result as JSON
print(json.dumps({"itinerary": optimal_itinerary}))