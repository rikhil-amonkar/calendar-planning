import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Financial District': {'Russian Hill': 10, 'Sunset District': 31, 'North Beach': 7, 'The Castro': 23, 'Golden Gate Park': 23},
    'Russian Hill': {'Financial District': 11, 'Sunset District': 23, 'North Beach': 5, 'The Castro': 21, 'Golden Gate Park': 21},
    'Sunset District': {'Financial District': 30, 'Russian Hill': 24, 'North Beach': 29, 'The Castro': 17, 'Golden Gate Park': 11},
    'North Beach': {'Financial District': 8, 'Russian Hill': 4, 'Sunset District': 27, 'The Castro': 22, 'Golden Gate Park': 22},
    'The Castro': {'Financial District': 20, 'Russian Hill': 18, 'Sunset District': 17, 'North Beach': 20, 'Golden Gate Park': 13},
    'Golden Gate Park': {'Financial District': 26, 'Russian Hill': 19, 'Sunset District': 10, 'North Beach': 24, 'The Castro': 13}
}

# Constraints
constraints = {
    'Ronald': {'location': 'Russian Hill','start_time': '13:45', 'end_time': '17:15','required_time': 105},
    'Patricia': {'location': 'Sunset District','start_time': '09:15', 'end_time': '22:00','required_time': 60},
    'Laura': {'location': 'North Beach','start_time': '12:30', 'end_time': '12:45','required_time': 15},
    'Emily': {'location': 'The Castro','start_time': '16:15', 'end_time': '18:30','required_time': 60},
    'Mary': {'location': 'Golden Gate Park','start_time': '15:00', 'end_time': '16:30','required_time': 60}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Financial District', location)
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