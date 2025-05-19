import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Nob Hill': {'Richmond District': 14, 'Financial District': 9, 'North Beach': 8, 'The Castro': 17, 'Golden Gate Park': 17},
    'Richmond District': {'Nob Hill': 17, 'Financial District': 22, 'North Beach': 17, 'The Castro': 16, 'Golden Gate Park': 9},
    'Financial District': {'Nob Hill': 8, 'Richmond District': 21, 'North Beach': 7, 'The Castro': 23, 'Golden Gate Park': 23},
    'North Beach': {'Nob Hill': 7, 'Richmond District': 18, 'Financial District': 8, 'The Castro': 22, 'Golden Gate Park': 22},
    'The Castro': {'Nob Hill': 16, 'Richmond District': 16, 'Financial District': 20, 'North Beach': 20, 'Golden Gate Park': 11},
    'Golden Gate Park': {'Nob Hill': 20, 'Richmond District': 7, 'Financial District': 26, 'North Beach': 24, 'The Castro': 13}
}

# Constraints
constraints = {
    'Emily': {'location': 'Richmond District','start_time': '19:00', 'end_time': '21:00','required_time': 15},
    'Margaret': {'location': 'Financial District','start_time': '16:30', 'end_time': '20:15','required_time': 75},
    'Ronald': {'location': 'North Beach','start_time': '18:30', 'end_time': '19:30','required_time': 45},
    'Deborah': {'location': 'The Castro','start_time': '13:45', 'end_time': '21:15','required_time': 90},
    'Jeffrey': {'location': 'Golden Gate Park','start_time': '11:15', 'end_time': '14:30','required_time': 120}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Nob Hill', location)
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