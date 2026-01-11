import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11
}

# Define constraints
start_time = datetime.strptime('9:00', '%H:%M')
karen_start = datetime.strptime('18:45', '%H:%M')
karen_end = datetime.strptime('20:15', '%H:%M')
mark_start = datetime.strptime('13:00', '%H:%M')
mark_end = datetime.strptime('17:45', '%H:%M')

# Minimum meeting durations in minutes
karen_min_duration = 90
mark_min_duration = 120

def calculate_meeting_slot(start_availability, end_availability, min_duration):
    """Calculate the earliest possible meeting slot that fits the minimum duration."""
    potential_start = start_availability
    potential_end = potential_start + timedelta(minutes=min_duration)
    if potential_end <= end_availability:
        return potential_start, potential_end
    return None, None

def format_time(time):
    """Format time in HH:MM without leading zeros."""
    return time.strftime('%-H:%M')

def generate_schedule():
    # Calculate possible meeting slots for Mark and Karen
    mark_meeting_start, mark_meeting_end = calculate_meeting_slot(mark_start, mark_end, mark_min_duration)
    karen_meeting_start, karen_meeting_end = calculate_meeting_slot(karen_start, karen_end, karen_min_duration)

    # Initialize itinerary
    itinerary = []

    # Try to meet Mark first
    if mark_meeting_start:
        # Check if we can reach Embarcadero in time
        travel_to_mark = travel_times[('North Beach', 'Embarcadero')]
        if start_time + timedelta(minutes=travel_to_mark) <= mark_meeting_start:
            # Add meeting with Mark to itinerary
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Mark",
                "start_time": format_time(mark_meeting_start),
                "end_time": format_time(mark_meeting_end)
            })
            # Update current time after meeting Mark and traveling back to North Beach
            current_time = mark_meeting_end + timedelta(minutes=travel_times[('Embarcadero', 'North Beach')])
        else:
            current_time = start_time

    # Try to meet Karen
    if karen_meeting_start:
        # Check if we can reach Pacific Heights in time
        travel_to_karen = travel_times[('North Beach', 'Pacific Heights')]
        if current_time + timedelta(minutes=travel_to_karen) <= karen_meeting_start:
            # Add meeting with Karen to itinerary
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Karen",
                "start_time": format_time(karen_meeting_start),
                "end_time": format_time(karen_meeting_end)
            })

    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=2)

# Generate and print the optimal meeting schedule
print(generate_schedule())