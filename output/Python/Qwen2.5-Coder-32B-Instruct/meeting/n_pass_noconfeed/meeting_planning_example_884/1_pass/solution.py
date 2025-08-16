import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def calculate_optimal_schedule():
    # Define travel times
    travel_times = {
        'Richmond District': {'Chinatown': 20, 'Sunset District': 11, 'Alamo Square': 13, 'Financial District': 22, 'North Beach': 17, 'Embarcadero': 19, 'Presidio': 7, 'Golden Gate Park': 9, 'Bayview': 27},
        'Chinatown': {'Richmond District': 20, 'Sunset District': 29, 'Alamo Square': 17, 'Financial District': 5, 'North Beach': 3, 'Embarcadero': 5, 'Presidio': 19, 'Golden Gate Park': 23, 'Bayview': 20},
        'Sunset District': {'Richmond District': 12, 'Chinatown': 30, 'Alamo Square': 17, 'Financial District': 30, 'North Beach': 28, 'Embarcadero': 30, 'Presidio': 16, 'Golden Gate Park': 11, 'Bayview': 22},
        'Alamo Square': {'Richmond District': 11, 'Chinatown': 15, 'Sunset District': 16, 'Financial District': 17, 'North Beach': 15, 'Embarcadero': 16, 'Presidio': 17, 'Golden Gate Park': 9, 'Bayview': 16},
        'Financial District': {'Richmond District': 21, 'Chinatown': 5, 'Sunset District': 30, 'Alamo Square': 17, 'North Beach': 7, 'Embarcadero': 4, 'Presidio': 22, 'Golden Gate Park': 23, 'Bayview': 19},
        'North Beach': {'Richmond District': 18, 'Chinatown': 6, 'Sunset District': 27, 'Alamo Square': 16, 'Financial District': 8, 'Embarcadero': 6, 'Presidio': 17, 'Golden Gate Park': 22, 'Bayview': 25},
        'Embarcadero': {'Richmond District': 21, 'Chinatown': 7, 'Sunset District': 30, 'Alamo Square': 19, 'Financial District': 5, 'North Beach': 5, 'Presidio': 20, 'Golden Gate Park': 25, 'Bayview': 21},
        'Presidio': {'Richmond District': 7, 'Chinatown': 21, 'Sunset District': 15, 'Alamo Square': 19, 'Financial District': 23, 'North Beach': 18, 'Embarcadero': 20, 'Golden Gate Park': 12, 'Bayview': 31},
        'Golden Gate Park': {'Richmond District': 7, 'Chinatown': 23, 'Sunset District': 10, 'Alamo Square': 9, 'Financial District': 26, 'North Beach': 23, 'Embarcadero': 25, 'Presidio': 11, 'Bayview': 23},
        'Bayview': {'Richmond District': 25, 'Chinatown': 19, 'Sunset District': 23, 'Alamo Square': 16, 'Financial District': 19, 'North Beach': 22, 'Embarcadero': 19, 'Presidio': 32, 'Golden Gate Park': 22}
    }

    # Define meeting constraints
    meetings = {
        'Robert': {'location': 'Chinatown', 'start': '7:45', 'end': '17:30', 'min_duration': 120},
        'David': {'location': 'Sunset District', 'start': '12:30', 'end': '19:45', 'min_duration': 45},
        'Matthew': {'location': 'Alamo Square', 'start': '8:45', 'end': '13:45', 'min_duration': 90},
        'Jessica': {'location': 'Financial District', 'start': '9:30', 'end': '18:45', 'min_duration': 45},
        'Melissa': {'location': 'North Beach', 'start': '7:15', 'end': '16:45', 'min_duration': 45},
        'Mark': {'location': 'Embarcadero', 'start': '15:15', 'end': '17:00', 'min_duration': 45},
        'Deborah': {'location': 'Presidio', 'start': '19:00', 'end': '19:45', 'min_duration': 45},
        'Karen': {'location': 'Golden Gate Park', 'start': '19:30', 'end': '22:00', 'min_duration': 120},
        'Laura': {'location': 'Bayview', 'start': '21:15', 'end': '22:15', 'min_duration': 15}
    }

    # Start time
    current_time = parse_time('9:00')
    current_location = 'Richmond District'
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, details in sorted_meetings:
        location = details['location']
        start_time = parse_time(details['start'])
        end_time = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can attend the meeting
        if arrival_time + timedelta(minutes=min_duration) <= end_time:
            # Adjust start time if we arrive early
            meeting_start_time = max(arrival_time, start_time)
            meeting_end_time = meeting_start_time + timedelta(minutes=min_duration)

            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': name,
                'start_time': format_time(meeting_start_time),
                'end_time': format_time(meeting_end_time)
            })

            # Update current time and location
            current_time = meeting_end_time
            current_location = location

    # Output the itinerary as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

calculate_optimal_schedule()