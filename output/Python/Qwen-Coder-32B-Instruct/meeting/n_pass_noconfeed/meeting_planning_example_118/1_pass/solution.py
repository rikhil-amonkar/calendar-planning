import json
from datetime import datetime, timedelta

def calculate_schedule():
    # Define the locations and their travel times
    travel_times = {
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Union Square'): 22
    }

    # Define the meeting constraints
    meetings = {
        'Richard': {'location': 'Union Square', 'start': '8:45', 'end': '13:00', 'min_duration': 120},
        'Charles': {'location': 'Presidio', 'start': '9:45', 'end': '13:00', 'min_duration': 120}
    }

    # Convert times to datetime objects for easier manipulation
    def parse_time(time_str):
        return datetime.strptime(time_str, '%H:%M')

    # Start time
    start_time = parse_time('9:00')
    current_location = 'Bayview'
    current_time = start_time
    itinerary = []

    # Function to add a meeting to the itinerary
    def add_meeting(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start.strftime('%H:%M'),
            "end_time": end.strftime('%H:%M')
        })

    # Try to meet Richard first if possible
    richard_start = parse_time(meetings['Richard']['start'])
    richard_end = parse_time(meetings['Richard']['end'])
    richard_min_duration = meetings['Richard']['min_duration']

    # Calculate the time needed to reach Richard's location
    travel_to_richard = travel_times[(current_location, meetings['Richard']['location'])]
    potential_start_with_richard = current_time + timedelta(minutes=travel_to_richard)

    if potential_start_with_richard <= richard_end - timedelta(minutes=richard_min_duration):
        # We can meet Richard
        meeting_start = max(potential_start_with_richard, richard_start)
        meeting_end = meeting_start + timedelta(minutes=richard_min_duration)
        add_meeting('Richard', meetings['Richard']['location'], meeting_start, meeting_end)
        current_time = meeting_end
        current_location = meetings['Richard']['location']
    else:
        # Cannot meet Richard for the required duration
        pass

    # Try to meet Charles next if possible
    charles_start = parse_time(meetings['Charles']['start'])
    charles_end = parse_time(meetings['Charles']['end'])
    charles_min_duration = meetings['Charles']['min_duration']

    # Calculate the time needed to reach Charles's location
    travel_to_charles = travel_times[(current_location, meetings['Charles']['location'])]
    potential_start_with_charles = current_time + timedelta(minutes=travel_to_charles)

    if potential_start_with_charles <= charles_end - timedelta(minutes=charles_min_duration):
        # We can meet Charles
        meeting_start = max(potential_start_with_charles, charles_start)
        meeting_end = meeting_start + timedelta(minutes=charles_min_duration)
        add_meeting('Charles', meetings['Charles']['location'], meeting_start, meeting_end)
    else:
        # Cannot meet Charles for the required duration
        pass

    # Output the itinerary as JSON
    print(json.dumps({"itinerary": itinerary}))

calculate_schedule()