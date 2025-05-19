import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Presidio': {'Fisherman\'s Wharf': 19, 'Alamo Square': 19, 'Financial District': 23, 'Union Square': 22, 'Sunset District': 15, 'Embarcadero': 20, 'Golden Gate Park': 12, 'Chinatown': 21, 'Richmond District': 7},
    'Fisherman\'s Wharf': {'Presidio': 17, 'Alamo Square': 21, 'Financial District': 11, 'Union Square': 13, 'Sunset District': 27, 'Embarcadero': 8, 'Golden Gate Park': 25, 'Chinatown': 12, 'Richmond District': 18},
    'Alamo Square': {'Presidio': 17, 'Fisherman\'s Wharf': 19, 'Financial District': 17, 'Union Square': 14, 'Sunset District': 16, 'Embarcadero': 16, 'Golden Gate Park': 9, 'Chinatown': 15, 'Richmond District': 11},
    'Financial District': {'Presidio': 22, 'Fisherman\'s Wharf': 10, 'Alamo Square': 17, 'Union Square': 9, 'Sunset District': 30, 'Embarcadero': 4, 'Golden Gate Park': 23, 'Chinatown': 5, 'Richmond District': 21},
    'Union Square': {'Presidio': 24, 'Fisherman\'s Wharf': 15, 'Alamo Square': 15, 'Financial District': 9, 'Sunset District': 27, 'Embarcadero': 11, 'Golden Gate Park': 22, 'Chinatown': 7, 'Richmond District': 20},
    'Sunset District': {'Presidio': 16, 'Fisherman\'s Wharf': 29, 'Alamo Square': 17, 'Financial District': 30, 'Union Square': 30, 'Embarcadero': 30, 'Golden Gate Park': 11, 'Chinatown': 30, 'Richmond District': 12},
    'Embarcadero': {'Presidio': 20, 'Fisherman\'s Wharf': 6, 'Alamo Square': 19, 'Financial District': 5, 'Union Square': 10, 'Sunset District': 30, 'Golden Gate Park': 25, 'Chinatown': 7, 'Richmond District': 21},
    'Golden Gate Park': {'Presidio': 11, 'Fisherman\'s Wharf': 24, 'Alamo Square': 9, 'Financial District': 26, 'Union Square': 22, 'Sunset District': 10, 'Embarcadero': 25, 'Chinatown': 23, 'Richmond District': 7},
    'Chinatown': {'Presidio': 19, 'Fisherman\'s Wharf': 8, 'Alamo Square': 17, 'Financial District': 5, 'Union Square': 7, 'Sunset District': 29, 'Embarcadero': 5, 'Golden Gate Park': 23, 'Richmond District': 20},
    'Richmond District': {'Presidio': 7, 'Fisherman\'s Wharf': 18, 'Alamo Square': 13, 'Financial District': 22, 'Union Square': 21, 'Sunset District': 11, 'Embarcadero': 19, 'Golden Gate Park': 9, 'Chinatown': 20}
}

# Constraints
constraints = {
    'Jeffrey': {'location': 'Fisherman\'s Wharf','start_time': '10:15', 'end_time': '13:00','required_time': 90},
    'Ronald': {'location': 'Alamo Square','start_time': '07:45', 'end_time': '14:45','required_time': 120},
    'Jason': {'location': 'Financial District','start_time': '10:45', 'end_time': '16:00','required_time': 105},
    'Melissa': {'location': 'Union Square','start_time': '17:45', 'end_time': '18:15','required_time': 15},
    'Elizabeth': {'location': 'Sunset District','start_time': '14:45', 'end_time': '17:30','required_time': 105},
    'Margaret': {'location': 'Embarcadero','start_time': '13:15', 'end_time': '19:00','required_time': 90},
    'George': {'location': 'Golden Gate Park','start_time': '19:00', 'end_time': '22:00','required_time': 75},
    'Richard': {'location': 'Chinatown','start_time': '09:30', 'end_time': '21:00','required_time': 15},
    'Laura': {'location': 'Richmond District','start_time': '09:45', 'end_time': '18:00','required_time': 60}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Presidio', location)
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