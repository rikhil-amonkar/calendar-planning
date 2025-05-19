import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Russian Hill'): 14,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Russian Hill'): 24,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Russian Hill'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Golden Gate Park'): 21,
}

# Meeting constraints
meetings = {
    'Rebecca': {'location': 'Presidio', 'start': '18:15', 'end': '20:45', 'duration': 60},
    'Linda': {'location': 'Sunset District', 'start': '15:30', 'end': '19:45', 'duration': 30},
    'Elizabeth': {'location': 'Haight-Ashbury', 'start': '17:15', 'end': '19:30', 'duration': 105},
    'William': {'location': 'Mission District', 'start': '13:15', 'end': '19:30', 'duration': 30},
    'Robert': {'location': 'Golden Gate Park', 'start': '14:15', 'end': '21:30', 'duration': 45},
    'Mark': {'location': 'Russian Hill', 'start': '10:00', 'end': '21:15', 'duration': 75},
}

# Start time at The Castro
start_time = datetime.strptime('9:00', '%H:%M')

# Helper function to convert time represented as string to datetime
def str_to_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Finding optimal meeting schedule
itinerary = []
current_time = start_time
visited_locations = set()

def can_meet(start, end, duration):
    return (end - start).total_seconds() / 60 >= duration

# Schedule meetings based on available time and travel times
for person, details in meetings.items():
    location = details['location']
    meeting_start = str_to_time(details['start'])
    meeting_end = str_to_time(details['end'])
    duration = details['duration']

    # Check if the current_time allows meeting this person
    travel_time = travel_times.get((current_time.strftime('%H:%M'), location), float('inf'))
    if current_time + timedelta(minutes=travel_time) <= meeting_end:
        # Check if we can meet
        actual_meeting_start = max(current_time + timedelta(minutes=travel_time), meeting_start)
        actual_meeting_end = actual_meeting_start + timedelta(minutes=duration)

        if can_meet(actual_meeting_start, actual_meeting_end, duration) and actual_meeting_end <= meeting_end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": actual_meeting_start.strftime('%H:%M'),
                "end_time": actual_meeting_end.strftime('%H:%M')
            })
            # Update the current time for next meeting after we meet
            current_time = actual_meeting_end
            visited_locations.add(location)

# Output result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))