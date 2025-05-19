import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Marina District': {'Mission District': 20, 'Fisherman\'s Wharf': 10, 'Presidio': 10, 'Union Square': 16, 'Sunset District': 19, 'Financial District': 17, 'Haight-Ashbury': 16, 'Russian Hill': 8},
    'Mission District': {'Marina District': 19, 'Fisherman\'s Wharf': 22, 'Presidio': 25, 'Union Square': 15, 'Sunset District': 24, 'Financial District': 15, 'Haight-Ashbury': 12, 'Russian Hill': 15},
    'Fisherman\'s Wharf': {'Marina District': 9, 'Mission District': 22, 'Presidio': 17, 'Union Square': 13, 'Sunset District': 27, 'Financial District': 11, 'Haight-Ashbury': 22, 'Russian Hill': 7},
    'Presidio': {'Marina District': 11, 'Mission District': 26, 'Fisherman\'s Wharf': 19, 'Union Square': 22, 'Sunset District': 15, 'Financial District': 23, 'Haight-Ashbury': 15, 'Russian Hill': 14},
    'Union Square': {'Marina District': 18, 'Mission District': 14, 'Fisherman\'s Wharf': 15, 'Presidio': 24, 'Sunset District': 27, 'Financial District': 9, 'Haight-Ashbury': 18, 'Russian Hill': 13},
    'Sunset District': {'Marina District': 21, 'Mission District': 25, 'Fisherman\'s Wharf': 29, 'Presidio': 16, 'Union Square': 30, 'Financial District': 30, 'Haight-Ashbury': 15, 'Russian Hill': 24},
    'Financial District': {'Marina District': 15, 'Mission District': 17, 'Fisherman\'s Wharf': 10, 'Presidio': 22, 'Union Square': 9, 'Sunset District': 30, 'Haight-Ashbury': 19, 'Russian Hill': 11},
    'Haight-Ashbury': {'Marina District': 17, 'Mission District': 11, 'Fisherman\'s Wharf': 23, 'Presidio': 15, 'Union Square': 19, 'Sunset District': 15, 'Financial District': 21, 'Russian Hill': 17},
    'Russian Hill': {'Marina District': 7, 'Mission District': 16, 'Fisherman\'s Wharf': 7, 'Presidio': 14, 'Union Square': 10, 'Sunset District': 23, 'Financial District': 11, 'Haight-Ashbury': 17}
}

# Constraints
constraints = {
    'Karen': {'location': 'Mission District','start_time': '14:15', 'end_time': '22:00','required_time': 30},
    'Richard': {'location': 'Fisherman\'s Wharf','start_time': '14:30', 'end_time': '17:30','required_time': 30},
    'Robert': {'location': 'Presidio','start_time': '21:45', 'end_time': '22:45','required_time': 60},
    'Joseph': {'location': 'Union Square','start_time': '11:45', 'end_time': '14:45','required_time': 120},
    'Helen': {'location': 'Sunset District','start_time': '14:45', 'end_time': '20:45','required_time': 105},
    'Elizabeth': {'location': 'Financial District','start_time': '10:00', 'end_time': '12:45','required_time': 75},
    'Kimberly': {'location': 'Haight-Ashbury','start_time': '14:15', 'end_time': '17:30','required_time': 105},
    'Ashley': {'location': 'Russian Hill','start_time': '11:30', 'end_time': '21:30','required_time': 45}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Marina District', location)
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