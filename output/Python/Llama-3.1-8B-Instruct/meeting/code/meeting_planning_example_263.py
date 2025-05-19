import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Bayview': {'Embarcadero': 19, 'Fisherman\'s Wharf': 25, 'Financial District': 19},
    'Embarcadero': {'Bayview': 21, 'Fisherman\'s Wharf': 6, 'Financial District': 5},
    'Fisherman\'s Wharf': {'Bayview': 26, 'Embarcadero': 8, 'Financial District': 11},
    'Financial District': {'Bayview': 19, 'Embarcadero': 4, 'Fisherman\'s Wharf': 10}
}

# Constraints
constraints = {
    'Betty': {'location': 'Embarcadero','start_time': '19:45', 'end_time': '21:45','required_time': 15},
    'Karen': {'location': 'Fisherman\'s Wharf','start_time': '08:45', 'end_time': '15:00','required_time': 30},
    'Anthony': {'location': 'Financial District','start_time': '09:15', 'end_time': '21:30','required_time': 105}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Bayview', location)
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