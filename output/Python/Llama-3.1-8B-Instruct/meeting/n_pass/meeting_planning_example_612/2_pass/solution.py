import json
import datetime
from itertools import combinations

# Define travel times in minutes
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

# Define meeting constraints
constraints = {
    'Emily': {'start_time': 1215, 'end_time': 1315,'min_meeting_time': 105},
    'Mark': {'start_time': 1745, 'end_time': 1930,'min_meeting_time': 60},
    'Deborah': {'start_time': 0730, 'end_time': 1330,'min_meeting_time': 45},
    'Margaret': {'start_time': 2130, 'end_time': 2230,'min_meeting_time': 60},
    'George': {'start_time': 0730, 'end_time': 1215,'min_meeting_time': 60},
    'Andrew': {'start_time': 2115, 'end_time': 2200,'min_meeting_time': 75},
    'Steven': {'start_time': 1115, 'end_time': 1915,'min_meeting_time': 105}
}

def calculate_arrival_time(start_time, travel_time):
    arrival_time = start_time + datetime.timedelta(minutes=travel_time)
    return arrival_time.strftime('%H:%M')

def calculate_meeting_time(start_time, end_time):
    meeting_time = (end_time - start_time).total_seconds() / 60
    return meeting_time

def check_meeting_constraints(meeting):
    person = meeting['person']
    start_time = meeting['start_time']
    end_time = meeting['end_time']
    min_meeting_time = constraints[person]['min_meeting_time']
    meeting_time = calculate_meeting_time(start_time, end_time)
    return meeting_time >= min_meeting_time

def generate_itinerary(locations):
    itinerary = []
    current_location = 'Alamo Square'
    start_time = datetime.datetime.strptime('0900', '%H%M')
    for location in locations:
        travel_time = travel_times[current_location][location]
        arrival_time = calculate_arrival_time(start_time, travel_time)
        itinerary.append({'action': 'travel', 'location': current_location, 'destination': location,'start_time': start_time.strftime('%H:%M'), 'end_time': arrival_time})
        current_location = location
        start_time = datetime.datetime.strptime(arrival_time, '%H:%M')
        if location in constraints:
            for person in constraints[location]:
                start_time_person = datetime.datetime.strptime(constraints[location][person]['start_time'], '%H%M')
                end_time_person = datetime.datetime.strptime(constraints[location][person]['end_time'], '%H%M')
                if start_time >= start_time_person and end_time_person >= start_time:
                    meeting_time = calculate_meeting_time(start_time, end_time_person)
                    meeting = {'action':'meet', 'location': location, 'person': person,'start_time': start_time.strftime('%H:%M'), 'end_time': (start_time + datetime.timedelta(minutes=meeting_time)).strftime('%H:%M')}
                    if check_meeting_constraints(meeting):
                        itinerary.append(meeting)
        start_time += datetime.timedelta(minutes=30)
    return itinerary

def find_optimal_itinerary(locations):
    optimal_itinerary = []
    for r in range(1, len(locations) + 1):
        for combination in combinations(locations, r):
            itinerary = generate_itinerary(combination)
            if len(itinerary) > len(optimal_itinerary):
                optimal_itinerary = itinerary
    return optimal_itinerary

def main():
    locations = list(constraints.keys())
    optimal_itinerary = find_optimal_itinerary(locations)
    optimal_itinerary.append({'action': 'travel', 'location': 'Alamo Square', 'destination': 'Alamo Square','start_time': '0900', 'end_time': '0900'})
    optimal_itinerary.append({'action': 'travel', 'location': 'Alamo Square', 'destination': 'Alamo Square','start_time': '1900', 'end_time': '1900'})
    optimal_itinerary_json = json.dumps(optimal_itinerary, indent=4)
    print('SOLUTION:')
    print(optimal_itinerary_json)

if __name__ == '__main__':
    main()