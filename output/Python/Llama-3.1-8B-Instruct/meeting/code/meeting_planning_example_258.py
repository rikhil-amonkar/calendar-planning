import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Embarcadero': {'Presidio': 20, 'Richmond District': 21, 'Fisherman\'s Wharf': 6},
    'Presidio': {'Embarcadero': 20, 'Richmond District': 7, 'Fisherman\'s Wharf': 19},
    'Richmond District': {'Embarcadero': 19, 'Presidio': 7, 'Fisherman\'s Wharf': 18},
    'Fisherman\'s Wharf': {'Embarcadero': 8, 'Presidio': 17, 'Richmond District': 18}
}

# Constraints
constraints = {
    'Betty': {'location': 'Presidio','start_time': '10:15', 'end_time': '21:30','required_time': 45},
    'David': {'location': 'Richmond District','start_time': '13:00', 'end_time': '20:15','required_time': 90},
    'Barbara': {'location': 'Fisherman\'s Wharf','start_time': '09:15', 'end_time': '20:15','required_time': 120}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Embarcadero', location)
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