import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Marina District': {'Bayview': 27, 'Sunset District': 19, 'Richmond District': 11, 'Nob Hill': 12, 'Chinatown': 15, 'Haight-Ashbury': 16, 'North Beach': 11, 'Russian Hill': 8, 'Embarcadero': 14},
    'Bayview': {'Marina District': 27, 'Sunset District': 23, 'Richmond District': 25, 'Nob Hill': 20, 'Chinatown': 19, 'Haight-Ashbury': 19, 'North Beach': 22, 'Russian Hill': 23, 'Embarcadero': 19},
    'Sunset District': {'Marina District': 21, 'Bayview': 22, 'Richmond District': 12, 'Nob Hill': 27, 'Chinatown': 30, 'Haight-Ashbury': 15, 'North Beach': 28, 'Russian Hill': 24, 'Embarcadero': 30},
    'Richmond District': {'Marina District': 9, 'Bayview': 27, 'Sunset District': 11, 'Nob Hill': 17, 'Chinatown': 20, 'Haight-Ashbury': 10, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19},
    'Nob Hill': {'Marina District': 11, 'Bayview': 19, 'Sunset District': 24, 'Richmond District': 14, 'Chinatown': 6, 'Haight-Ashbury': 13, 'North Beach': 8, 'Russian Hill': 5, 'Embarcadero': 9},
    'Chinatown': {'Marina District': 12, 'Bayview': 20, 'Sunset District': 29, 'Richmond District': 20, 'Nob Hill': 9, 'Haight-Ashbury': 19, 'North Beach': 3, 'Russian Hill': 7, 'Embarcadero': 5},
    'Haight-Ashbury': {'Marina District': 17, 'Bayview': 18, 'Sunset District': 15, 'Richmond District': 10, 'Nob Hill': 15, 'Chinatown': 19, 'North Beach': 19, 'Russian Hill': 17, 'Embarcadero': 20},
    'North Beach': {'Marina District': 9, 'Bayview': 25, 'Sunset District': 27, 'Richmond District': 18, 'Nob Hill': 7, 'Chinatown': 6, 'Haight-Ashbury': 18, 'Russian Hill': 4, 'Embarcadero': 6},
    'Russian Hill': {'Marina District': 7, 'Bayview': 23, 'Sunset District': 23, 'Richmond District': 14, 'Nob Hill': 5, 'Chinatown': 9, 'Haight-Ashbury': 17, 'North Beach': 5, 'Embarcadero': 8},
    'Embarcadero': {'Marina District': 12, 'Bayview': 21, 'Sunset District': 30, 'Richmond District': 21, 'Nob Hill': 10, 'Chinatown': 7, 'Haight-Ashbury': 21, 'North Beach': 5, 'Russian Hill': 8}
}

# Constraints
constraints = {
    'Charles': {'location': 'Bayview','start_time': '11:30', 'end_time': '14:30','required_time': 45},
    'Robert': {'location': 'Sunset District','start_time': '16:45', 'end_time': '21:00','required_time': 30},
    'Karen': {'location': 'Richmond District','start_time': '19:15', 'end_time': '21:30','required_time': 60},
    'Rebecca': {'location': 'Nob Hill','start_time': '16:15', 'end_time': '20:30','required_time': 90},
    'Margaret': {'location': 'Chinatown','start_time': '14:15', 'end_time': '20:45','required_time': 120},
    'Patricia': {'location': 'Haight-Ashbury','start_time': '14:30', 'end_time': '20:30','required_time': 45},
    'Mark': {'location': 'North Beach','start_time': '14:00', 'end_time': '18:30','required_time': 105},
    'Melissa': {'location': 'Russian Hill','start_time': '13:00', 'end_time': '20:45','required_time': 30},
    'Laura': {'location': 'Embarcadero','start_time': '07:45', 'end_time': '13:15','required_time': 105}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Marina District', location)
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