from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Bayview': {'Midtown': 30, 'Downtown': 45},
    'Midtown': {'Bayview': 30, 'Downtown': 15, 'Uptown': 30},
    'Downtown': {'Bayview': 45, 'Midtown': 15, 'Uptown': 45},
    'Uptown': {'Midtown': 30, 'Downtown': 45}
}

# Define constraints for each person
constraints = {
    'Alice': {'location': 'Midtown', 'start': '10:00', 'end': '12:00', 'min_duration': 30},
    'Bob': {'location': 'Downtown', 'start': '11:00', 'end': '13:00', 'min_duration': 45},
    'Charlie': {'location': 'Uptown', 'start': '10:30', 'end': '12:30', 'min_duration': 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def find_meeting_time(constraints, travel_times):
    # Find the latest start time and the earliest end time
    latest_start = max(parse_time(person['start']) for person in constraints.values())
    earliest_end = min(parse_time(person['end']) for person in constraints.values())

    # Check if there is enough time for a meeting
    if (earliest_end - latest_start).seconds < max(person['min_duration'] * 60 for person in constraints.values()):
        return "No suitable meeting time found."

    # Try to find a location where everyone can meet within their constraints
    for location in travel_times:
        can_meet = True
        for person, details in constraints.items():
            # Calculate the travel time from the person's location to the proposed meeting location
            travel_time = travel_times[details['location']].get(location, float('inf'))
            # Calculate the available time after travel
            available_time = (parse_time(details['end']) - parse_time(details['start'])).seconds - travel_time * 60
            # Check if the person can stay for the minimum duration
            if available_time < details['min_duration'] * 60:
                can_meet = False
                break
        if can_meet:
            return f"Meeting can be held at {location} starting from {latest_start.strftime('%H:%M')}."

    return "No suitable meeting time or location found."

# Example usage
meeting_time = find_meeting_time(constraints, travel_times)
print(meeting_time)