from datetime import datetime, timedelta

# Example data structures for demonstration purposes
constraints = {
    'Alice': {'location': 'Park', 'min_duration': 30, 'end': '14:00'},
    'Bob': {'location': 'Cafe', 'min_duration': 60, 'end': '15:00'}
}

travel_times = {
    ('Home', 'Park'): 10,
    ('Home', 'Cafe'): 15,
    ('Park', 'Cafe'): 5
}

def parse_time(time_str):
    """Convert time string to datetime object assuming today's date."""
    return datetime.strptime(f"{datetime.now().date()} {time_str}", "%Y-%m-%d %H:%M")

def can_meet(person, current_time):
    """Check if it's possible to meet the person at the current time."""
    # This is a placeholder function; implement actual logic as needed
    return True

def next_location(current_time, current_loc):
    options = []
    for person, constraint in constraints.items():
        if can_meet(person, current_time):
            # Check if the current location is the same as the target location
            if current_loc == constraint['location']:
                travel_time = 0
            else:
                travel_time = travel_times.get((current_loc, constraint['location']), float('inf'))
            meet_start = current_time + timedelta(minutes=travel_time)
            meet_end = meet_start + timedelta(minutes=constraint['min_duration'])
            if parse_time(constraint['end']) >= meet_end:
                options.append((person, meet_start, meet_end))
    return sorted(options, key=lambda x: x[1])

# Example usage
current_time = datetime.now()
current_loc = 'Home'
print(next_location(current_time, current_loc))