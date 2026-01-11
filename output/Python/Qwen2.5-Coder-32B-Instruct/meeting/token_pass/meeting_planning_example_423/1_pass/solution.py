import heapq
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Presidio': {'Richmond District': 7, 'North Beach': 18, 'Financial District': 23, 'Golden Gate Park': 12, 'Union Square': 22},
    'Richmond District': {'Presidio': 7, 'North Beach': 17, 'Financial District': 22, 'Golden Gate Park': 9, 'Union Square': 21},
    'North Beach': {'Presidio': 17, 'Richmond District': 18, 'Financial District': 7, 'Golden Gate Park': 22, 'Union Square': 7},
    'Financial District': {'Presidio': 22, 'Richmond District': 21, 'North Beach': 7, 'Golden Gate Park': 23, 'Union Square': 9},
    'Golden Gate Park': {'Presidio': 11, 'Richmond District': 7, 'North Beach': 24, 'Financial District': 26, 'Union Square': 22},
    'Union Square': {'Presidio': 24, 'Richmond District': 20, 'North Beach': 10, 'Financial District': 9, 'Golden Gate Park': 22}
}

# Define meeting constraints
meeting_constraints = {
    'Jason': {'location': 'Richmond District', 'start': '13:00', 'end': '20:45', 'duration': 90},
    'Melissa': {'location': 'North Beach', 'start': '18:45', 'end': '20:15', 'duration': 45},
    'Brian': {'location': 'Financial District', 'start': '09:45', 'end': '21:45', 'duration': 15},
    'Elizabeth': {'location': 'Golden Gate Park', 'start': '08:45', 'end': '21:30', 'duration': 105},
    'Laura': {'location': 'Union Square', 'start': '14:15', 'end': '19:30', 'duration': 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes_to_time(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def get_meeting_slots(constraints):
    slots = []
    for person, details in constraints.items():
        start_time = parse_time(details['start'])
        end_time = parse_time(details['end'])
        duration = details['duration']
        location = details['location']
        # Generate all possible slots for this person
        current_time = start_time
        while current_time + timedelta(minutes=duration) <= end_time:
            slots.append((current_time, current_time + timedelta(minutes=duration), person, location))
            current_time += timedelta(minutes=1)
    return slots

def find_optimal_schedule(slots, travel_times):
    slots.sort()  # Sort slots by start time
    current_time = parse_time('09:00')
    current_location = 'Presidio'
    itinerary = []

    for start, end, person, location in slots:
        # Calculate travel time from current location to meeting location
        travel_time = travel_times[current_location][location]
        # Check if we can reach the meeting location in time
        if add_minutes_to_time(current_time, travel_time) <= start:
            # Update current time and location
            current_time = add_minutes_to_time(current_time, travel_time)
            current_location = location
            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(start),
                "end_time": format_time(end)
            })
            # Update current time to end of meeting
            current_time = end
    return itinerary

def main():
    slots = get_meeting_slots(meeting_constraints)
    itinerary = find_optimal_schedule(slots, travel_times)
    result = {
        "itinerary": itinerary
    }
    import json
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()