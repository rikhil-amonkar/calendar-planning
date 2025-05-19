import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Richmond District': {'Marina District': 9, 'Chinatown': 20, 'Financial District': 22, 'Bayview': 26, 'Union Square': 21},
    'Marina District': {'Richmond District': 11, 'Chinatown': 16, 'Financial District': 17, 'Bayview': 27, 'Union Square': 16},
    'Chinatown': {'Richmond District': 20, 'Marina District': 12, 'Financial District': 5, 'Bayview': 22, 'Union Square': 7},
    'Financial District': {'Richmond District': 21, 'Marina District': 15, 'Chinatown': 5, 'Bayview': 19, 'Union Square': 9},
    'Bayview': {'Richmond District': 25, 'Marina District': 25, 'Chinatown': 18, 'Financial District': 19, 'Union Square': 17},
    'Union Square': {'Richmond District': 20, 'Marina District': 18, 'Chinatown': 7, 'Financial District': 9, 'Bayview': 15}
}

# Constraints
constraints = {
    'Kimberly': {'location': 'Marina District','start_time': '13:15', 'end_time': '16:45','required_time': 15},
    'Robert': {'location': 'Chinatown','start_time': '12:15', 'end_time': '20:15','required_time': 15},
    'Rebecca': {'location': 'Financial District','start_time': '13:15', 'end_time': '16:45','required_time': 75},
    'Margaret': {'location': 'Bayview','start_time': '09:30', 'end_time': '13:30','required_time': 30},
    'Kenneth': {'location': 'Union Square','start_time': '19:30', 'end_time': '21:15','required_time': 75}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Richmond District', location)
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