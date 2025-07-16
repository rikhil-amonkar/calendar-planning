import json
from itertools import permutations

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Travel times in minutes (from -> to)
    travel_times = {
        'Bayview': {
            'Embarcadero': 19,
            'Richmond District': 25,
            'Fisherman\'s Wharf': 25
        },
        'Embarcadero': {
            'Bayview': 21,
            'Richmond District': 21,
            'Fisherman\'s Wharf': 6
        },
        'Richmond District': {
            'Bayview': 26,
            'Embarcadero': 19,
            'Fisherman\'s Wharf': 18
        },
        'Fisherman\'s Wharf': {
            'Bayview': 26,
            'Embarcadero': 8,
            'Richmond District': 18
        }
    }

    # Meeting constraints
    constraints = [
        {
            'person': 'Jessica',
            'location': 'Embarcadero',
            'available_start': '16:45',
            'available_end': '19:00',
            'min_duration': 30
        },
        {
            'person': 'Sandra',
            'location': 'Richmond District',
            'available_start': '18:30',
            'available_end': '21:45',
            'min_duration': 120
        },
        {
            'person': 'Jason',
            'location': 'Fisherman\'s Wharf',
            'available_start': '16:00',
            'available_end': '16:45',
            'min_duration': 30
        }
    ]

    current_location = 'Bayview'
    current_time = time_to_minutes('9:00')
    itinerary = []

    # Try all possible orders of meeting people
    best_itinerary = None
    max_meetings = 0

    for order in permutations(constraints):
        temp_itinerary = []
        temp_location = current_location
        temp_time = current_time
        meetings_count = 0

        for person in order:
            # Check if we can meet this person
            location = person['location']
            travel_time = travel_times[temp_location][location]
            arrival_time = temp_time + travel_time

            available_start = time_to_minutes(person['available_start'])
            available_end = time_to_minutes(person['available_end'])
            min_duration = person['min_duration']

            # Calculate meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + min_duration

            if meeting_end <= available_end:
                # We can meet this person
                meetings_count += 1
                temp_itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': person['person'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                temp_location = location
                temp_time = meeting_end
            else:
                # Can't meet this person in this order
                break

        if meetings_count > max_meetings:
            max_meetings = meetings_count
            best_itinerary = temp_itinerary

    return {'itinerary': best_itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))