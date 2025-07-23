import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Alamo Square': {
            'Russian Hill': 13,
            'Presidio': 18,
            'Chinatown': 16,
            'Sunset District': 16,
            'The Castro': 8,
            'Embarcadero': 17,
            'Golden Gate Park': 9
        },
        'Russian Hill': {
            'Alamo Square': 15,
            'Presidio': 14,
            'Chinatown': 9,
            'Sunset District': 23,
            'The Castro': 21,
            'Embarcadero': 8,
            'Golden Gate Park': 21
        },
        'Presidio': {
            'Alamo Square': 18,
            'Russian Hill': 14,
            'Chinatown': 21,
            'Sunset District': 15,
            'The Castro': 21,
            'Embarcadero': 20,
            'Golden Gate Park': 12
        },
        'Chinatown': {
            'Alamo Square': 17,
            'Russian Hill': 7,
            'Presidio': 19,
            'Sunset District': 29,
            'The Castro': 22,
            'Embarcadero': 5,
            'Golden Gate Park': 23
        },
        'Sunset District': {
            'Alamo Square': 17,
            'Russian Hill': 24,
            'Presidio': 16,
            'Chinatown': 30,
            'The Castro': 17,
            'Embarcadero': 31,
            'Golden Gate Park': 11
        },
        'The Castro': {
            'Alamo Square': 8,
            'Russian Hill': 18,
            'Presidio': 20,
            'Chinatown': 20,
            'Sunset District': 17,
            'Embarcadero': 22,
            'Golden Gate Park': 11
        },
        'Embarcadero': {
            'Alamo Square': 19,
            'Russian Hill': 8,
            'Presidio': 20,
            'Chinatown': 7,
            'Sunset District': 30,
            'The Castro': 25,
            'Golden Gate Park': 25
        },
        'Golden Gate Park': {
            'Alamo Square': 10,
            'Russian Hill': 19,
            'Presidio': 11,
            'Chinatown': 23,
            'Sunset District': 10,
            'The Castro': 13,
            'Embarcadero': 25
        }
    }

    # Define friend constraints
    friends = [
        {
            'name': 'Emily',
            'location': 'Russian Hill',
            'available_start': '12:15',
            'available_end': '14:15',
            'min_duration': 105
        },
        {
            'name': 'Mark',
            'location': 'Presidio',
            'available_start': '14:45',
            'available_end': '19:30',
            'min_duration': 60
        },
        {
            'name': 'Deborah',
            'location': 'Chinatown',
            'available_start': '7:30',
            'available_end': '15:30',
            'min_duration': 45
        },
        {
            'name': 'Margaret',
            'location': 'Sunset District',
            'available_start': '21:30',
            'available_end': '22:30',
            'min_duration': 60
        },
        {
            'name': 'George',
            'location': 'The Castro',
            'available_start': '7:30',
            'available_end': '14:15',
            'min_duration': 60
        },
        {
            'name': 'Andrew',
            'location': 'Embarcadero',
            'available_start': '20:15',
            'available_end': '22:00',
            'min_duration': 75
        },
        {
            'name': 'Steven',
            'location': 'Golden Gate Park',
            'available_start': '11:15',
            'available_end': '21:15',
            'min_duration': 105
        }
    ]

    # Current time starts at 9:00 AM at Alamo Square
    current_time = time_to_minutes('9:00')
    current_location = 'Alamo Square'
    itinerary = []

    # Sort friends by their available end time (earlier first)
    friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x['available_end']))

    # Try to schedule each friend
    for friend in friends_sorted:
        loc = friend['location']
        travel_time = travel_times[current_location][loc]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']

        # Calculate possible meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + min_duration, available_end)

        if meeting_end - meeting_start >= min_duration:
            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': loc,
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = loc

    # Check if we can fit Margaret (who has very late availability)
    margaret = next(f for f in friends if f['name'] == 'Margaret')
    loc = margaret['location']
    travel_time = travel_times[current_location][loc]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(margaret['available_start'])
    available_end = time_to_minutes(margaret['available_end'])
    min_duration = margaret['min_duration']

    meeting_start = max(arrival_time, available_start)
    meeting_end = min(meeting_start + min_duration, available_end)

    if meeting_end - meeting_start >= min_duration:
        itinerary.append({
            'action': 'meet',
            'location': loc,
            'person': margaret['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })

    return {'itinerary': itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))