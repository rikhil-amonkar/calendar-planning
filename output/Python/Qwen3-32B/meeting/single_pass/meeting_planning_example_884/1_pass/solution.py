import itertools
import json

# Define the friends with their constraints
friends = [
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start_time': 465,  # 7:45 AM
        'end_time': 1050,   # 5:30 PM
        'duration': 120
    },
    {
        'name': 'David',
        'location': 'Sunset District',
        'start_time': 750,  # 12:30 PM
        'end_time': 1185,   # 7:45 PM
        'duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Alamo Square',
        'start_time': 525,  # 8:45 AM
        'end_time': 825,    # 1:45 PM
        'duration': 90
    },
    {
        'name': 'Jessica',
        'location': 'Financial District',
        'start_time': 570,  # 9:30 AM
        'end_time': 1125,   # 6:45 PM
        'duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'start_time': 435,  # 7:15 AM
        'end_time': 1005,   # 4:45 PM
        'duration': 45
    },
    {
        'name': 'Mark',
        'location': 'Embarcadero',
        'start_time': 915,  # 3:15 PM
        'end_time': 1020,   # 5:00 PM
        'duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'Presidio',
        'start_time': 1140, # 7:00 PM
        'end_time': 1185,   # 7:45 PM
        'duration': 45
    },
    {
        'name': 'Karen',
        'location': 'Golden Gate Park',
        'start_time': 1170, # 7:30 PM
        'end_time': 1320,   # 10:00 PM
        'duration': 120
    },
    {
        'name': 'Laura',
        'location': 'Bayview',
        'start_time': 1275, # 9:15 PM
        'end_time': 1335,   # 10:15 PM
        'duration': 15
    }
]

# Define travel times between locations
travel_time = {
    'Richmond District': {
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27
    },
    'Chinatown': {
        'Richmond District': 20,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'North Beach': 8,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Bayview': 22
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22
    }
}

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def find_best_itinerary(friends, travel_time):
    best_itinerary = []
    max_length = 0

    for perm in itertools.permutations(friends):
        current_time = 540  # 9:00 AM in minutes
        current_location = 'Richmond District'
        itinerary_details = []
        valid = True

        for friend in perm:
            if current_location not in travel_time or friend['location'] not in travel_time[current_location]:
                valid = False
                break
            travel_duration = travel_time[current_location][friend['location']]
            arrival_time = current_time + travel_duration

            if arrival_time + friend['duration'] > friend['end_time']:
                valid = False
                break

            meeting_start = max(arrival_time, friend['start_time'])
            meeting_end = meeting_start + friend['duration']

            itinerary_details.append({
                'name': friend['name'],
                'location': friend['location'],
                'start': meeting_start,
                'end': meeting_end
            })

            current_time = meeting_end
            current_location = friend['location']

        if valid and len(itinerary_details) > max_length:
            max_length = len(itinerary_details)
            best_itinerary = itinerary_details

    return best_itinerary

def format_itinerary(itinerary_details):
    itinerary = []
    for detail in itinerary_details:
        itinerary.append({
            "action": "meet",
            "location": detail['location'],
            "person": detail['name'],
            "start_time": minutes_to_time_str(detail['start']),
            "end_time": minutes_to_time_str(detail['end'])
        })
    return {"itinerary": itinerary}

def main():
    best_itinerary = find_best_itinerary(friends, travel_time)
    result = format_itinerary(best_itinerary)
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()