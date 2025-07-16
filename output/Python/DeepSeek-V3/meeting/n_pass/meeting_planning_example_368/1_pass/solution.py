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
        'Bayview': {'Russian Hill': 23, 'Alamo Square': 16, 'North Beach': 21, 'Financial District': 19},
        'Russian Hill': {'Bayview': 23, 'Alamo Square': 15, 'North Beach': 5, 'Financial District': 11},
        'Alamo Square': {'Bayview': 16, 'Russian Hill': 13, 'North Beach': 15, 'Financial District': 17},
        'North Beach': {'Bayview': 22, 'Russian Hill': 4, 'Alamo Square': 16, 'Financial District': 8},
        'Financial District': {'Bayview': 19, 'Russian Hill': 10, 'Alamo Square': 17, 'North Beach': 7}
    }

    # Constraints
    start_location = 'Bayview'
    start_time = time_to_minutes('9:00')

    people = [
        {'name': 'Joseph', 'location': 'Russian Hill', 'start': time_to_minutes('8:30'), 'end': time_to_minutes('19:15'), 'duration': 60},
        {'name': 'Nancy', 'location': 'Alamo Square', 'start': time_to_minutes('11:00'), 'end': time_to_minutes('16:00'), 'duration': 90},
        {'name': 'Jason', 'location': 'North Beach', 'start': time_to_minutes('16:45'), 'end': time_to_minutes('21:45'), 'duration': 15},
        {'name': 'Jeffrey', 'location': 'Financial District', 'start': time_to_minutes('10:30'), 'end': time_to_minutes('15:45'), 'duration': 45}
    ]

    best_itinerary = []
    max_meetings = 0

    # Try all permutations of people to find the best order
    for order in permutations(people):
        current_location = start_location
        current_time = start_time
        itinerary = []
        meetings = 0

        for person in order:
            travel_time = travel_times[current_location][person['location']]
            arrival_time = current_time + travel_time

            # Calculate meeting window
            meeting_start = max(arrival_time, person['start'])
            meeting_end = meeting_start + person['duration']

            if meeting_end > person['end']:
                continue  # Can't meet this person in this order

            itinerary.append({
                'action': 'meet',
                'location': person['location'],
                'person': person['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings += 1
            current_time = meeting_end
            current_location = person['location']

        if meetings > max_meetings or (meetings == max_meetings and len(itinerary) > len(best_itinerary)):
            max_meetings = meetings
            best_itinerary = itinerary

    return {'itinerary': best_itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))