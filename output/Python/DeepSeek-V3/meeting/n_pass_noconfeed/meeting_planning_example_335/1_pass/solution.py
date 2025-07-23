import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times in minutes (from -> to)
    travel_times = {
        'Pacific Heights': {
            'North Beach': 9,
            'Financial District': 13,
            'Alamo Square': 10,
            'Mission District': 15
        },
        'North Beach': {
            'Pacific Heights': 8,
            'Financial District': 8,
            'Alamo Square': 16,
            'Mission District': 18
        },
        'Financial District': {
            'Pacific Heights': 13,
            'North Beach': 7,
            'Alamo Square': 17,
            'Mission District': 17
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'North Beach': 15,
            'Financial District': 17,
            'Mission District': 10
        },
        'Mission District': {
            'Pacific Heights': 16,
            'North Beach': 17,
            'Financial District': 17,
            'Alamo Square': 11
        }
    }

    # Constraints
    constraints = [
        {
            'person': 'Helen',
            'location': 'North Beach',
            'available_start': '9:00',
            'available_end': '17:00',
            'min_duration': 15
        },
        {
            'person': 'Betty',
            'location': 'Financial District',
            'available_start': '19:00',
            'available_end': '21:45',
            'min_duration': 90
        },
        {
            'person': 'Amanda',
            'location': 'Alamo Square',
            'available_start': '19:45',
            'available_end': '21:00',
            'min_duration': 60
        },
        {
            'person': 'Kevin',
            'location': 'Mission District',
            'available_start': '10:45',
            'available_end': '14:45',
            'min_duration': 45
        }
    ]

    current_location = 'Pacific Heights'
    current_time = time_to_minutes('9:00')
    itinerary = []

    # Try all permutations to find the best order
    best_itinerary = None
    max_meetings = 0

    for order in permutations(constraints):
        temp_itinerary = []
        temp_location = current_location
        temp_time = current_time
        meetings_count = 0

        for person_data in order:
            location = person_data['location']
            travel_time = travel_times[temp_location][location]
            arrival_time = temp_time + travel_time

            available_start = time_to_minutes(person_data['available_start'])
            available_end = time_to_minutes(person_data['available_end'])
            min_duration = person_data['min_duration']

            # Calculate meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + min_duration

            if meeting_end <= available_end:
                temp_itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': person_data['person'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings_count += 1
                temp_time = meeting_end
                temp_location = location
            else:
                break

        if meetings_count > max_meetings:
            max_meetings = meetings_count
            best_itinerary = temp_itinerary

    return best_itinerary

def main():
    itinerary = calculate_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()