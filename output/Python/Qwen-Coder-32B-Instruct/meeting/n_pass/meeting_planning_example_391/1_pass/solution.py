import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Financial District'): 30,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Financial District'): 17,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Presidio'): 22,
}

# Define meeting constraints
meetings = {
    'Kevin': {'location': 'Alamo Square', 'start': '8:15', 'end': '21:30', 'min_duration': 75},
    'Kimberly': {'location': 'Russian Hill', 'start': '8:45', 'end': '12:30', 'min_duration': 30},
    'Joseph': {'location': 'Presidio', 'start': '18:30', 'end': '19:15', 'min_duration': 45},
    'Thomas': {'location': 'Financial District', 'start': '19:00', 'end': '21:45', 'min_duration': 45},
}

# Convert time strings to datetime objects
def time_to_dt(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if two time intervals overlap and calculate overlap duration
def overlap(start1, end1, start2, end2):
    latest_start = max(start1, start2)
    earliest_end = min(end1, end2)
    overlap_duration = (earliest_end - latest_start).total_seconds() / 60
    return overlap_duration if overlap_duration > 0 else 0

# Main function to find the optimal schedule
def find_optimal_schedule():
    current_location = 'Sunset District'
    current_time = time_to_dt('9:00')
    itinerary = []

    # Sort meetings by their start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: time_to_dt(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = time_to_dt(details['start'])
        end = time_to_dt(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]

        # Check if we can reach the location in time and meet the minimum duration requirement
        potential_start = current_time + timedelta(minutes=travel_time)
        potential_end = potential_start + timedelta(minutes=min_duration)

        if potential_start < start:
            potential_start = start
            potential_end = potential_start + timedelta(minutes=min_duration)

        if potential_end <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": potential_start.strftime('%H:%M'),
                "end_time": potential_end.strftime('%H:%M')
            })
            current_time = potential_end
            current_location = location

    return itinerary

# Generate the schedule and print it as JSON
optimal_schedule = find_optimal_schedule()
print(json.dumps({"itinerary": optimal_schedule}))