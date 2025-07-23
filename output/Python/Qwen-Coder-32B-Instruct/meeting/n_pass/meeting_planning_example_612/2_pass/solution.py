import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Embarcadero'): 31,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Embarcadero'): 25,
}

# Define meeting constraints
meetings = {
    'Emily': {'location': 'Russian Hill', 'start': '12:15', 'end': '14:15', 'min_duration': 105},
    'Mark': {'location': 'Presidio', 'start': '14:45', 'end': '19:30', 'min_duration': 60},
    'Deborah': {'location': 'Chinatown', 'start': '07:30', 'end': '15:30', 'min_duration': 45},
    'Margaret': {'location': 'Sunset District', 'start': '21:30', 'end': '22:30', 'min_duration': 60},
    'George': {'location': 'The Castro', 'start': '07:30', 'end': '14:15', 'min_duration': 60},
    'Andrew': {'location': 'Embarcadero', 'start': '20:15', 'end': '22:00', 'min_duration': 75},
    'Steven': {'location': 'Golden Gate Park', 'start': '11:15', 'end': '21:15', 'min_duration': 105},
}

# Convert times to datetime objects
def convert_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate total time available for meetings
start_time = convert_to_datetime('09:00')
end_time = convert_to_datetime('23:59')

# Function to check if a meeting can fit within the schedule
def can_fit_meeting(current_time, current_location, meeting):
    meeting_start = convert_to_datetime(meeting['start'])
    meeting_end = convert_to_datetime(meeting['end'])
    min_duration = meeting['min_duration']
    
    # Check if there's a travel time entry for the current location to the meeting location
    if (current_location, meeting['location']) not in travel_times:
        return None
    
    travel_time = travel_times[(current_location, meeting['location'])]
    
    potential_start = max(current_time + timedelta(minutes=travel_time), meeting_start)
    potential_end = potential_start + timedelta(minutes=min_duration)
    
    if potential_end <= meeting_end and potential_end <= end_time:
        return potential_start, potential_end
    return None

# Main function to find the optimal schedule
def find_optimal_schedule():
    current_time = start_time
    current_location = 'Alamo Square'
    itinerary = []
    
    # Sort meetings by start time
    sorted_meetings = sorted(meetings.values(), key=lambda x: convert_to_datetime(x['start']))
    
    for meeting in sorted_meetings:
        fit = can_fit_meeting(current_time, current_location, meeting)
        if fit:
            start, end = fit
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': [k for k, v in meetings.items() if v == meeting][0],
                'start_time': start.strftime('%H:%M'),
                'end_time': end.strftime('%H:%M')
            })
            current_time = end
            current_location = meeting['location']
    
    return itinerary

# Generate the itinerary
itinerary = find_optimal_schedule()

# Output the result as JSON
result = {
    "itinerary": itinerary
}

print(json.dumps(result))