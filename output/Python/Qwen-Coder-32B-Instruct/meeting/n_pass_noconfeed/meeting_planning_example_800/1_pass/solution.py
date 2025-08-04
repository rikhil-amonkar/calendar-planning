import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Mission District'): 11,
}

# Define meeting constraints
meetings = {
    'Melissa': {'location': 'The Castro', 'start': '20:15', 'end': '21:15', 'min_duration': 30},
    'Kimberly': {'location': 'North Beach', 'start': '7:00', 'end': '10:30', 'min_duration': 15},
    'Joseph': {'location': 'Embarcadero', 'start': '15:30', 'end': '19:30', 'min_duration': 75},
    'Barbara': {'location': 'Alamo Square', 'start': '20:45', 'end': '21:45', 'min_duration': 15},
    'Kenneth': {'location': 'Nob Hill', 'start': '12:15', 'end': '17:15', 'min_duration': 105},
    'Joshua': {'location': 'Presidio', 'start': '16:30', 'end': '18:15', 'min_duration': 105},
    'Brian': {'location': 'Fisherman\'s Wharf', 'start': '9:30', 'end': '15:30', 'min_duration': 45},
    'Steven': {'location': 'Mission District', 'start': '19:30', 'end': '21:00', 'min_duration': 90},
    'Betty': {'location': 'Haight-Ashbury', 'start': '19:00', 'end': '20:30', 'min_duration': 90},
}

# Convert times to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def can_meet(start, end, min_duration, current_time):
    available_start = max(parse_time(start), current_time)
    available_end = parse_time(end)
    available_duration = (available_end - available_start).seconds // 60
    return available_duration >= min_duration

def find_next_meeting(current_location, current_time, meetings_left):
    best_meeting = None
    best_duration = 0
    best_travel_time = float('inf')
    
    for person, details in meetings_left.items():
        location = details['location']
        start = details['start']
        end = details['end']
        min_duration = details['min_duration']
        
        if can_meet(start, end, min_duration, current_time):
            travel_time = travel_times[(current_location, location)]
            meeting_start = max(parse_time(start), current_time + timedelta(minutes=travel_time))
            meeting_end = parse_time(end)
            duration = (meeting_end - meeting_start).seconds // 60
            
            if duration >= min_duration and (duration > best_duration or (duration == best_duration and travel_time < best_travel_time)):
                best_meeting = person
                best_duration = duration
                best_travel_time = travel_time
    
    return best_meeting

def create_schedule():
    itinerary = []
    current_location = 'Union Square'
    current_time = parse_time('9:00')
    meetings_left = meetings.copy()
    
    while meetings_left:
        next_meeting = find_next_meeting(current_location, current_time, meetings_left)
        
        if next_meeting:
            details = meetings_left.pop(next_meeting)
            location = details['location']
            start = details['start']
            end = details['end']
            min_duration = details['min_duration']
            
            travel_time = travel_times[(current_location, location)]
            meeting_start = max(parse_time(start), current_time + timedelta(minutes=travel_time))
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": next_meeting,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            
            current_location = location
            current_time = meeting_end
        else:
            break
    
    return itinerary

schedule = create_schedule()
result = {"itinerary": schedule}
print(json.dumps(result))