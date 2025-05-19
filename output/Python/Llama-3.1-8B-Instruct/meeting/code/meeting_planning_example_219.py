import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'The Castro': {'Alamo Square': 8, 'Union Square': 19, 'Chinatown': 20},
    'Alamo Square': {'The Castro': 8, 'Union Square': 14, 'Chinatown': 16},
    'Union Square': {'The Castro': 19, 'Alamo Square': 15, 'Chinatown': 7},
    'Chinatown': {'The Castro': 22, 'Alamo Square': 17, 'Union Square': 7}
}

# Constraints
constraints = {
    'Emily': {'location': 'Alamo Square','start_time': '11:45', 'end_time': '15:15','required_time': 105},
    'Barbara': {'location': 'Union Square','start_time': '16:45', 'end_time': '18:15','required_time': 60},
    'William': {'location': 'Chinatown','start_time': '17:15', 'end_time': '19:00','required_time': 105}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('The Castro', location)
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