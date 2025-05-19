import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Haight-Ashbury': {'Fisherman\'s Wharf': 23, 'Richmond District': 10, 'Mission District': 11, 'Bayview': 18},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Richmond District': 18, 'Mission District': 22, 'Bayview': 26},
    'Richmond District': {'Haight-Ashbury': 10, 'Fisherman\'s Wharf': 18, 'Mission District': 20, 'Bayview': 26},
    'Mission District': {'Haight-Ashbury': 12, 'Fisherman\'s Wharf': 22, 'Richmond District': 20, 'Bayview': 15},
    'Bayview': {'Haight-Ashbury': 19, 'Fisherman\'s Wharf': 25, 'Richmond District': 25, 'Mission District': 13}
}

# Constraints
constraints = {
    'Sarah': {'location': 'Fisherman\'s Wharf','start_time': '14:45', 'end_time': '17:30','required_time': 105},
    'Mary': {'location': 'Richmond District','start_time': '13:00', 'end_time': '19:15','required_time': 75},
    'Helen': {'location': 'Mission District','start_time': '21:45', 'end_time': '22:30','required_time': 30},
    'Thomas': {'location': 'Bayview','start_time': '15:15', 'end_time': '18:45','required_time': 120}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Haight-Ashbury', location)
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