import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4,
}

# Define meeting constraints
meetings = {
    'Anthony': {'location': 'Chinatown', 'start': '13:15', 'end': '14:30', 'min_duration': 60},
    'Rebecca': {'location': 'Russian Hill', 'start': '19:30', 'end': '21:15', 'min_duration': 105},
    'Melissa': {'location': 'North Beach', 'start': '8:15', 'end': '13:30', 'min_duration': 105},
}

# Convert time strings to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

# Calculate the time difference in minutes between two time objects
def time_difference(start, end):
    start_dt = datetime.combine(datetime.today(), start)
    end_dt = datetime.combine(datetime.today(), end)
    return int((end_dt - start_dt).total_seconds() // 60)

# Find the best meeting time within the given constraints
def find_best_meeting_time(location, arrival_time, end, min_duration):
    start_dt = datetime.combine(datetime.today(), arrival_time)
    end_dt = datetime.combine(datetime.today(), end)
    for t in range(time_difference(arrival_time, end) - min_duration + 1):
        meeting_start = start_dt + timedelta(minutes=t)
        meeting_end = meeting_start + timedelta(minutes=min_duration)
        if meeting_start.time() >= arrival_time and meeting_end.time() <= end:
            return meeting_start.time(), meeting_end.time()
    return None, None

# Main function to compute the optimal meeting schedule
def compute_schedule():
    current_location = 'Sunset District'
    current_time = time_to_datetime('9:00')
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: time_to_datetime(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = time_to_datetime(details['start'])
        end = time_to_datetime(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next meeting location
        travel_time = travel_times[(current_location, location)]
        arrival_time = (datetime.combine(datetime.today(), current_time) + timedelta(minutes=travel_time)).time()

        # Ensure the arrival time is not later than the meeting start time
        if arrival_time > start:
            arrival_time = start

        # Find the best meeting time within the constraints
        meeting_start, meeting_end = find_best_meeting_time(location, arrival_time, end, min_duration)

        # If no valid meeting time can be found, try to reschedule the meeting later
        while not meeting_start or not meeting_end:
            # Increment the arrival time by 1 minute and try again
            arrival_time = (datetime.combine(datetime.today(), arrival_time) + timedelta(minutes=1)).time()
            meeting_start, meeting_end = find_best_meeting_time(location, arrival_time, end, min_duration)

        # Add travel action to the itinerary
        itinerary.append({
            "action": "travel",
            "location": location,
            "person": None,
            "start_time": current_time.strftime('%H:%M'),
            "end_time": arrival_time.strftime('%H:%M')
        })

        # Add meeting action to the itinerary
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": meeting_start.strftime('%H:%M'),
            "end_time": meeting_end.strftime('%H:%M')
        })

        # Update current location and time
        current_location = location
        current_time = meeting_end

    return itinerary

# Generate the schedule and output it as JSON
schedule = compute_schedule()
output = {
    "itinerary": schedule
}
print(json.dumps(output, indent=4))