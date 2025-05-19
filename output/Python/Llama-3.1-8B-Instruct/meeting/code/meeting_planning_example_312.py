import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Richmond District': {'Sunset District': 11, 'Haight-Ashbury': 10, 'Mission District': 20, 'Golden Gate Park': 9},
    'Sunset District': {'Richmond District': 12, 'Haight-Ashbury': 15, 'Mission District': 24, 'Golden Gate Park': 11},
    'Haight-Ashbury': {'Richmond District': 10, 'Sunset District': 15, 'Mission District': 11, 'Golden Gate Park': 7},
    'Mission District': {'Richmond District': 20, 'Sunset District': 24, 'Haight-Ashbury': 12, 'Golden Gate Park': 17},
    'Golden Gate Park': {'Richmond District': 7, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Mission District': 17}
}

# Constraints
constraints = {
    'Sarah': {'location': 'Sunset District','start_time': '10:45', 'end_time': '19:00','required_time': 30},
    'Richard': {'location': 'Haight-Ashbury','start_time': '11:45', 'end_time': '15:45','required_time': 90},
    'Elizabeth': {'location': 'Mission District','start_time': '11:00', 'end_time': '17:15','required_time': 120},
    'Michelle': {'location': 'Golden Gate Park','start_time': '18:15', 'end_time': '20:45','required_time': 90}
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