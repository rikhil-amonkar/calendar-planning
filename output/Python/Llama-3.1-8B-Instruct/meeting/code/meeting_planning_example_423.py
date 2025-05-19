import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Presidio': {'Richmond District': 7, 'North Beach': 18, 'Financial District': 23, 'Golden Gate Park': 12, 'Union Square': 22},
    'Richmond District': {'Presidio': 7, 'North Beach': 17, 'Financial District': 22, 'Golden Gate Park': 9, 'Union Square': 21},
    'North Beach': {'Presidio': 17, 'Richmond District': 18, 'Financial District': 8, 'Golden Gate Park': 22, 'Union Square': 7},
    'Financial District': {'Presidio': 22, 'Richmond District': 21, 'North Beach': 7, 'Golden Gate Park': 23, 'Union Square': 9},
    'Golden Gate Park': {'Presidio': 11, 'Richmond District': 7, 'North Beach': 24, 'Financial District': 26, 'Union Square': 22},
    'Union Square': {'Presidio': 24, 'Richmond District': 20, 'North Beach': 10, 'Financial District': 9, 'Golden Gate Park': 22}
}

# Constraints
constraints = {
    'Jason': {'location': 'Richmond District','start_time': '13:00', 'end_time': '20:45','required_time': 90},
    'Melissa': {'location': 'North Beach','start_time': '18:45', 'end_time': '20:15','required_time': 45},
    'Brian': {'location': 'Financial District','start_time': '09:45', 'end_time': '21:45','required_time': 15},
    'Elizabeth': {'location': 'Golden Gate Park','start_time': '08:45', 'end_time': '21:30','required_time': 105},
    'Laura': {'location': 'Union Square','start_time': '14:15', 'end_time': '19:30','required_time': 75}
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