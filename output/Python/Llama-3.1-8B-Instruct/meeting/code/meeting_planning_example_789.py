import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Union Square': {'Russian Hill': 13, 'Alamo Square': 15, 'Haight-Ashbury': 18, 'Marina District': 18, 'Bayview': 15, 'Chinatown': 7, 'Presidio': 24, 'Sunset District': 27},
    'Russian Hill': {'Union Square': 10, 'Alamo Square': 15, 'Haight-Ashbury': 17, 'Marina District': 7, 'Bayview': 23, 'Chinatown': 9, 'Presidio': 14, 'Sunset District': 23},
    'Alamo Square': {'Union Square': 14, 'Russian Hill': 13, 'Haight-Ashbury': 5, 'Marina District': 15, 'Bayview': 16, 'Chinatown': 15, 'Presidio': 17, 'Sunset District': 16},
    'Haight-Ashbury': {'Union Square': 19, 'Russian Hill': 17, 'Alamo Square': 5, 'Marina District': 17, 'Bayview': 18, 'Chinatown': 19, 'Presidio': 15, 'Sunset District': 15},
    'Marina District': {'Union Square': 16, 'Russian Hill': 8, 'Alamo Square': 15, 'Haight-Ashbury': 16, 'Bayview': 27, 'Chinatown': 15, 'Presidio': 10, 'Sunset District': 19},
    'Bayview': {'Union Square': 18, 'Russian Hill': 23, 'Alamo Square': 16, 'Haight-Ashbury': 19, 'Marina District': 27, 'Chinatown': 19, 'Presidio': 32, 'Sunset District': 23},
    'Chinatown': {'Union Square': 7, 'Russian Hill': 7, 'Alamo Square': 17, 'Haight-Ashbury': 19, 'Marina District': 12, 'Bayview': 20, 'Presidio': 19, 'Sunset District': 29},
    'Presidio': {'Union Square': 22, 'Russian Hill': 14, 'Alamo Square': 19, 'Haight-Ashbury': 15, 'Marina District': 11, 'Bayview': 31, 'Chinatown': 21, 'Sunset District': 15},
    'Sunset District': {'Union Square': 30, 'Russian Hill': 24, 'Alamo Square': 17, 'Haight-Ashbury': 15, 'Marina District': 21, 'Bayview': 22, 'Chinatown': 30, 'Presidio': 16}
}

# Constraints
constraints = {
    'Betty': {'location': 'Russian Hill','start_time': '07:00', 'end_time': '16:45','required_time': 105},
    'Melissa': {'location': 'Alamo Square','start_time': '09:30', 'end_time': '17:15','required_time': 105},
    'Joshua': {'location': 'Haight-Ashbury','start_time': '12:15', 'end_time': '19:00','required_time': 90},
    'Jeffrey': {'location': 'Marina District','start_time': '12:15', 'end_time': '18:00','required_time': 45},
    'James': {'location': 'Bayview','start_time': '07:30', 'end_time': '20:00','required_time': 90},
    'Anthony': {'location': 'Chinatown','start_time': '11:45', 'end_time': '13:30','required_time': 75},
    'Timothy': {'location': 'Presidio','start_time': '12:30', 'end_time': '14:45','required_time': 90},
    'Emily': {'location': 'Sunset District','start_time': '19:30', 'end_time': '21:30','required_time': 120}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Union Square', location)
    start_time = (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=travel_time)).strftime('%H:%M')
    end_time = (datetime.strptime(end_time, '%H:%M') + timedelta(minutes=travel_time)).strftime('%H:%M')
    return is_valid_meeting(person, start_time, end_time, required_time)

def generate_itinerary():
    itinerary = []
    start_time = '09:00'
    end_time = '12:00'
    
    for person in constraints:
        location = constraints[person]['location']
        start_person_time = constraints[person]['start_time']
        end_person_time = constraints[person]['end_time']
        required_time = constraints[person]['required_time']
        
        if schedule_meeting(person, start_time, end_time, required_time, location):
            itinerary.append({
                'action':'meet',
                'location': location,
                'person': person,
  'start_time': start_time,
                'end_time': end_time
            })
            start_time = end_time
            end_time = (datetime.strptime(end_person_time, '%H:%M') + timedelta(minutes=required_time)).strftime('%H:%M')
    
    return itinerary

def main():
    itinerary = generate_itinerary()
    print(json.dumps({'itinerary': itinerary}, indent=4))

if __name__ == '__main__':
    main()