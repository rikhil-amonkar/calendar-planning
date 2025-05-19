import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Fisherman\'s Wharf': {'The Castro': 26, 'Golden Gate Park': 25, 'Embarcadero': 8, 'Russian Hill': 7, 'Nob Hill': 11, 'Alamo Square': 20, 'North Beach': 6},
    'The Castro': {'Fisherman\'s Wharf': 24, 'Golden Gate Park': 11, 'Embarcadero': 22, 'Russian Hill': 18, 'Nob Hill': 16, 'Alamo Square': 8, 'North Beach': 20},
    'Golden Gate Park': {'Fisherman\'s Wharf': 24, 'The Castro': 13, 'Embarcadero': 25, 'Russian Hill': 19, 'Nob Hill': 20, 'Alamo Square': 10, 'North Beach': 24},
    'Embarcadero': {'Fisherman\'s Wharf': 6, 'The Castro': 25, 'Golden Gate Park': 25, 'Russian Hill': 8, 'Nob Hill': 10, 'Alamo Square': 19, 'North Beach': 5},
    'Russian Hill': {'Fisherman\'s Wharf': 7, 'The Castro': 21, 'Golden Gate Park': 21, 'Embarcadero': 8, 'Nob Hill': 5, 'Alamo Square': 15, 'North Beach': 5},
    'Nob Hill': {'Fisherman\'s Wharf': 11, 'The Castro': 17, 'Golden Gate Park': 17, 'Embarcadero': 9, 'Russian Hill': 5, 'Alamo Square': 11, 'North Beach': 8},
    'Alamo Square': {'Fisherman\'s Wharf': 19, 'The Castro': 8, 'Golden Gate Park': 9, 'Embarcadero': 17, 'Russian Hill': 13, 'Nob Hill': 11, 'North Beach': 16},
    'North Beach': {'Fisherman\'s Wharf': 5, 'The Castro': 22, 'Golden Gate Park': 22, 'Embarcadero': 6, 'Russian Hill': 4, 'Nob Hill': 7, 'Alamo Square': 16}
}

# Constraints
constraints = {
    'Laura': {'location': 'The Castro','start_time': '19:45', 'end_time': '21:30','required_time': 105},
    'Daniel': {'location': 'Golden Gate Park','start_time': '21:15', 'end_time': '21:45','required_time': 15},
    'William': {'location': 'Embarcadero','start_time': '07:00', 'end_time': '09:00','required_time': 90},
    'Karen': {'location': 'Russian Hill','start_time': '14:30', 'end_time': '19:45','required_time': 30},
    'Stephanie': {'location': 'Nob Hill','start_time': '07:30', 'end_time': '09:30','required_time': 45},
    'Joseph': {'location': 'Alamo Square','start_time': '11:30', 'end_time': '12:45','required_time': 15},
    'Kimberly': {'location': 'North Beach','start_time': '15:45', 'end_time': '19:15','required_time': 30}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Fisherman\'s Wharf', location)
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