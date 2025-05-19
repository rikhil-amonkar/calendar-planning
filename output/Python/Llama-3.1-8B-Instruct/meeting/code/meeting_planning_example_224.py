import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Fisherman\'s Wharf': {'Golden Gate Park': 25, 'Presidio': 17, 'Richmond District': 18},
    'Golden Gate Park': {'Fisherman\'s Wharf': 24, 'Presidio': 11, 'Richmond District': 7},
    'Presidio': {'Fisherman\'s Wharf': 19, 'Golden Gate Park': 12, 'Richmond District': 7},
    'Richmond District': {'Fisherman\'s Wharf': 18, 'Golden Gate Park': 9, 'Presidio': 7}
}

# Constraints
constraints = {
    'Melissa': {'location': 'Golden Gate Park','start_time': '08:30', 'end_time': '20:00','required_time': 15},
    'Nancy': {'location': 'Presidio','start_time': '19:45', 'end_time': '22:00','required_time': 105},
    'Emily': {'location': 'Richmond District','start_time': '16:45', 'end_time': '22:00','required_time': 120}
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