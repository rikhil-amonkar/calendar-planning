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
    # Define travel times in minutes
    travel_times = {
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Financial District'): 19,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Financial District'): 11,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Russian Hill'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7,
    }

    # Define constraints
    people = [
        {
            'name': 'Joseph',
            'location': 'Russian Hill',
            'available_start': '8:30',
            'available_end': '19:15',
            'duration': 60
        },
        {
            'name': 'Nancy',
            'location': 'Alamo Square',
            'available_start': '11:00',
            'available_end': '16:00',
            'duration': 90
        },
        {
            'name': 'Jason',
            'location': 'North Beach',
            'available_start': '16:45',
            'available_end': '21:45',
            'duration': 15
        },
        {
            'name': 'Jeffrey',
            'location': 'Financial District',
            'available_start': '10:30',
            'available_end': '15:45',
            'duration': 45
        }
    ]

    current_location = 'Bayview'
    current_time = time_to_minutes('9:00')
    best_itinerary = []
    max_meetings = 0

    # Try all permutations of people to find the best schedule
    for order in permutations(people):
        itinerary = []
        temp_location = current_location
        temp_time = current_time
        meetings = 0

        for person in order:
            # Calculate travel time to person's location
            travel_key = (temp_location, person['location'])
            travel_time = travel_times.get(travel_key, 0)
            arrival_time = temp_time + travel_time

            # Check if we can meet the person
            available_start = time_to_minutes(person['available_start'])
            available_end = time_to_minutes(person['available_end'])
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + person['duration']

            if meeting_end <= available_end:
                # Add meeting to itinerary
                itinerary.append({
                    'action': 'meet',
                    'location': person['location'],
                    'person': person['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                temp_location = person['location']
                temp_time = meeting_end
                meetings += 1
            else:
                # Can't meet this person in this order
                break

        if meetings > max_meetings:
            max_meetings = meetings
            best_itinerary = itinerary
        elif meetings == max_meetings and meetings > 0:
            # Prefer the itinerary that ends earlier
            if temp_time < time_to_minutes(best_itinerary[-1]['end_time']):
                best_itinerary = itinerary

    return {'itinerary': best_itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))