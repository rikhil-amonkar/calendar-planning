import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Embarcadero': 11,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'Fisherman\'s Wharf': 15,
        'Mission District': 14,
        'Haight-Ashbury': 18,
    },
    'The Castro': {
        'Union Square': 19,
        'North Beach': 20,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Fisherman\'s Wharf': 24,
        'Mission District': 7,
        'Haight-Ashbury': 6,
    },
    'North Beach': {
        'Union Square': 7,
        'The Castro': 23,
        'Embarcadero': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Mission District': 18,
        'Haight-Ashbury': 18,
    },
    'Embarcadero': {
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Fisherman\'s Wharf': 6,
        'Mission District': 20,
        'Haight-Ashbury': 21,
    },
    'Alamo Square': {
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Embarcadero': 16,
        'Nob Hill': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 19,
        'Mission District': 10,
        'Haight-Ashbury': 5,
    },
    'Nob Hill': {
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Embarcadero': 9,
        'Alamo Square': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 10,
        'Mission District': 13,
        'Haight-Ashbury': 13,
    },
    'Presidio': {
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Embarcadero': 20,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Mission District': 26,
        'Haight-Ashbury': 15,
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Embarcadero': 8,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Mission District': 22,
        'Haight-Ashbury': 22,
    },
    'Mission District': {
        'Union Square': 15,
        'The Castro': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Alamo Square': 11,
        'Nob Hill': 12,
        'Presidio': 25,
        'Fisherman\'s Wharf': 22,
        'Haight-Ashbury': 12,
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'The Castro': 6,
        'North Beach': 19,
        'Embarcadero': 20,
        'Alamo Square': 5,
        'Nob Hill': 15,
        'Presidio': 15,
        'Fisherman\'s Wharf': 23,
        'Mission District': 11,
    },
}

# Meeting constraints
meetings = {
    'Melissa': {'location': 'The Castro', 'start_time': '20:15', 'end_time': '21:15', 'duration': 30},
    'Kimberly': {'location': 'North Beach', 'start_time': '07:00', 'end_time': '10:30', 'duration': 15},
    'Joseph': {'location': 'Embarcadero', 'start_time': '15:30', 'end_time': '19:30', 'duration': 75},
    'Barbara': {'location': 'Alamo Square', 'start_time': '20:45', 'end_time': '21:45', 'duration': 15},
    'Kenneth': {'location': 'Nob Hill', 'start_time': '12:15', 'end_time': '17:15', 'duration': 105},
    'Joshua': {'location': 'Presidio', 'start_time': '16:30', 'end_time': '18:15', 'duration': 105},
    'Brian': {'location': 'Fisherman\'s Wharf', 'start_time': '09:30', 'end_time': '15:30', 'duration': 45},
    'Steven': {'location': 'Mission District', 'start_time': '19:00', 'end_time': '20:30', 'duration': 90},
    'Betty': {'location': 'Haight-Ashbury', 'start_time': '19:00', 'end_time': '20:30', 'duration': 90},
}

def time_in_minutes(time_str):
    """ Convert HH:MM time format to minutes since midnight. """
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """ Convert minutes since midnight back to HH:MM time format. """
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def schedule_meetings():
    start_time = time_in_minutes('9:00')
    itinerary = []

    # Meeting order based on constraints
    meetings_order = [
        ('Kimberly', 'North Beach'),
        ('Brian', 'Fisherman\'s Wharf'),
        ('Joseph', 'Embarcadero'),
        ('Kenneth', 'Nob Hill'),
        ('Joshua', 'Presidio'),
        ('Melissa', 'The Castro'),
        ('Barbara', 'Alamo Square'),
        ('Steven', 'Mission District'),
        ('Betty', 'Haight-Ashbury')
    ]

    current_time = start_time

    for person, location in meetings_order:
        meeting_info = meetings[person]
        meeting_start = time_in_minutes(meeting_info['start_time'])
        meeting_end = time_in_minutes(meeting_info['end_time'])

        if current_time < meeting_start:
            current_time = meeting_start

        # Calculate travel time to the location
        travel_time = travel_times['Union Square'].get(location, 0)
        current_time += travel_time

        # Check if we can fit this meeting
        if current_time + meeting_info['duration'] <= meeting_end:
            # Schedule the meeting
            meeting_start_time = current_time
            meeting_end_time = current_time + meeting_info['duration']
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(meeting_start_time),
                "end_time": minutes_to_time(meeting_end_time),
            })
            current_time = meeting_end_time  # Update the current time to after the meeting

            # Return to Union Square after meeting
            travel_back_time = travel_times[location]['Union Square']
            current_time += travel_back_time

    return {'itinerary': itinerary}

# Generate meeting schedule
optimal_schedule = schedule_meetings()

# Output the result in JSON format
print(json.dumps(optimal_schedule, indent=2))