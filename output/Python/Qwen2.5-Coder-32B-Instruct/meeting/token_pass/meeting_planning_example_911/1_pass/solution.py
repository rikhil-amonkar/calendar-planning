import json
from datetime import datetime, timedelta

# Define travel times as a dictionary
travel_times = {
    'The Castro': {'North Beach': 20, 'Golden Gate Park': 11, 'Embarcadero': 22, 'Haight-Ashbury': 6, 'Richmond District': 16, 'Nob Hill': 16, 'Marina District': 21, 'Presidio': 20, 'Union Square': 19, 'Financial District': 21},
    'North Beach': {'The Castro': 23, 'Golden Gate Park': 22, 'Embarcadero': 6, 'Haight-Ashbury': 18, 'Richmond District': 18, 'Nob Hill': 7, 'Marina District': 9, 'Presidio': 17, 'Union Square': 7, 'Financial District': 8},
    'Golden Gate Park': {'The Castro': 13, 'North Beach': 23, 'Embarcadero': 25, 'Haight-Ashbury': 7, 'Richmond District': 7, 'Nob Hill': 20, 'Marina District': 16, 'Presidio': 11, 'Union Square': 22, 'Financial District': 26},
    'Embarcadero': {'The Castro': 25, 'North Beach': 5, 'Golden Gate Park': 25, 'Haight-Ashbury': 20, 'Richmond District': 19, 'Nob Hill': 10, 'Marina District': 12, 'Presidio': 20, 'Union Square': 10, 'Financial District': 5},
    'Haight-Ashbury': {'The Castro': 6, 'North Beach': 19, 'Golden Gate Park': 7, 'Embarcadero': 20, 'Richmond District': 10, 'Nob Hill': 15, 'Marina District': 17, 'Presidio': 15, 'Union Square': 19, 'Financial District': 21},
    'Richmond District': {'The Castro': 16, 'North Beach': 17, 'Golden Gate Park': 9, 'Embarcadero': 19, 'Haight-Ashbury': 10, 'Nob Hill': 17, 'Marina District': 9, 'Presidio': 7, 'Union Square': 21, 'Financial District': 22},
    'Nob Hill': {'The Castro': 17, 'North Beach': 8, 'Golden Gate Park': 17, 'Embarcadero': 9, 'Haight-Ashbury': 13, 'Richmond District': 14, 'Marina District': 11, 'Presidio': 17, 'Union Square': 7, 'Financial District': 9},
    'Marina District': {'The Castro': 22, 'North Beach': 11, 'Golden Gate Park': 18, 'Embarcadero': 14, 'Haight-Ashbury': 16, 'Richmond District': 11, 'Nob Hill': 12, 'Presidio': 10, 'Union Square': 16, 'Financial District': 17},
    'Presidio': {'The Castro': 21, 'North Beach': 18, 'Golden Gate Park': 12, 'Embarcadero': 20, 'Haight-Ashbury': 15, 'Richmond District': 7, 'Nob Hill': 18, 'Marina District': 11, 'Union Square': 22, 'Financial District': 23},
    'Union Square': {'The Castro': 17, 'North Beach': 10, 'Golden Gate Park': 22, 'Embarcadero': 11, 'Haight-Ashbury': 18, 'Richmond District': 20, 'Nob Hill': 9, 'Marina District': 18, 'Presidio': 24, 'Financial District': 9},
    'Financial District': {'The Castro': 20, 'North Beach': 7, 'Golden Gate Park': 23, 'Embarcadero': 4, 'Haight-Ashbury': 19, 'Richmond District': 21, 'Nob Hill': 8, 'Marina District': 15, 'Presidio': 22, 'Union Square': 9}
}

# Define meeting constraints
meetings = {
    'Steven': {'location': 'North Beach', 'start': '17:30', 'end': '20:30', 'min_duration': 15},
    'Sarah': {'location': 'Golden Gate Park', 'start': '17:00', 'end': '19:15', 'min_duration': 75},
    'Brian': {'location': 'Embarcadero', 'start': '14:15', 'end': '16:00', 'min_duration': 105},
    'Stephanie': {'location': 'Haight-Ashbury', 'start': '10:15', 'end': '12:15', 'min_duration': 75},
    'Melissa': {'location': 'Richmond District', 'start': '14:00', 'end': '19:30', 'min_duration': 30},
    'Nancy': {'location': 'Nob Hill', 'start': '08:15', 'end': '12:45', 'min_duration': 90},
    'David': {'location': 'Marina District', 'start': '11:15', 'end': '13:15', 'min_duration': 120},
    'James': {'location': 'Presidio', 'start': '15:00', 'end': '18:15', 'min_duration': 120},
    'Elizabeth': {'location': 'Union Square', 'start': '11:30', 'end': '21:00', 'min_duration': 60},
    'Robert': {'location': 'Financial District', 'start': '13:15', 'end': '15:15', 'min_duration': 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def can_meet(current_time, meeting):
    start_time = parse_time(meeting['start'])
    end_time = parse_time(meeting['end'])
    min_duration = timedelta(minutes=meeting['min_duration'])
    required_end = current_time + min_duration
    return start_time <= current_time <= end_time and required_end <= end_time

def add_meeting(itinerary, location, person, start_time, end_time):
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start_time.strftime('%H:%M'),
        "end_time": end_time.strftime('%H:%M')
    })

def calculate_schedule():
    itinerary = []
    current_location = 'The Castro'
    current_time = parse_time('9:00')

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, meeting in sorted_meetings:
        location = meeting['location']
        start_time = parse_time(meeting['start'])
        end_time = parse_time(meeting['end'])
        min_duration = timedelta(minutes=meeting['min_duration'])

        # Calculate travel time to the meeting location
        travel_time = timedelta(minutes=travel_times[current_location][location])

        # Check if we can travel to the location and meet within the constraints
        if current_time + travel_time <= start_time:
            # We can travel to the location and meet within the constraints
            meeting_start = start_time
            meeting_end = meeting_start + min_duration
            add_meeting(itinerary, location, person, meeting_start, meeting_end)

            # Update current location and time
            current_location = location
            current_time = meeting_end
        elif current_time + travel_time + min_duration <= end_time:
            # We can travel to the location and meet within the constraints but after the meeting start time
            meeting_start = current_time + travel_time
            meeting_end = meeting_start + min_duration
            add_meeting(itinerary, location, person, meeting_start, meeting_end)

            # Update current location and time
            current_location = location
            current_time = meeting_end

    return itinerary

# Calculate and print the schedule
schedule = calculate_schedule()
print(json.dumps({"itinerary": schedule}, indent=2))