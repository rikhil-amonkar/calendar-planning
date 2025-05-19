import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Marina District': {'Embarcadero': 14, 'Bayview': 27, 'Union Square': 16, 'Chinatown': 15, 'Sunset District': 19, 'Golden Gate Park': 18, 'Financial District': 17, 'Haight-Ashbury': 16, 'Mission District': 20},
    'Embarcadero': {'Marina District': 12, 'Bayview': 21, 'Union Square': 10, 'Chinatown': 7, 'Sunset District': 30, 'Golden Gate Park': 25, 'Financial District': 5, 'Haight-Ashbury': 21, 'Mission District': 20},
    'Bayview': {'Marina District': 27, 'Embarcadero': 19, 'Union Square': 18, 'Chinatown': 19, 'Sunset District': 23, 'Golden Gate Park': 22, 'Financial District': 19, 'Haight-Ashbury': 19, 'Mission District': 13},
    'Union Square': {'Marina District': 18, 'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7, 'Sunset District': 27, 'Golden Gate Park': 22, 'Financial District': 9, 'Haight-Ashbury': 18, 'Mission District': 14},
    'Chinatown': {'Marina District': 12, 'Embarcadero': 5, 'Bayview': 20, 'Union Square': 7, 'Sunset District': 29, 'Golden Gate Park': 23, 'Financial District': 5, 'Haight-Ashbury': 19, 'Mission District': 17},
    'Sunset District': {'Marina District': 21, 'Embarcadero': 30, 'Bayview': 22, 'Union Square': 30, 'Chinatown': 30, 'Golden Gate Park': 11, 'Financial District': 30, 'Haight-Ashbury': 15, 'Mission District': 25},
    'Golden Gate Park': {'Marina District': 16, 'Embarcadero': 25, 'Bayview': 23, 'Union Square': 22, 'Chinatown': 23, 'Sunset District': 10, 'Financial District': 26, 'Haight-Ashbury': 7, 'Mission District': 17},
    'Financial District': {'Marina District': 15, 'Embarcadero': 4, 'Bayview': 19, 'Union Square': 9, 'Chinatown': 5, 'Sunset District': 30, 'Golden Gate Park': 23, 'Haight-Ashbury': 19, 'Mission District': 17},
    'Haight-Ashbury': {'Marina District': 17, 'Embarcadero': 20, 'Bayview': 18, 'Union Square': 19, 'Chinatown': 19, 'Sunset District': 15, 'Golden Gate Park': 7, 'Financial District': 21, 'Mission District': 11},
    'Mission District': {'Marina District': 19, 'Embarcadero': 19, 'Bayview': 14, 'Union Square': 15, 'Chinatown': 16, 'Sunset District': 24, 'Golden Gate Park': 17, 'Financial District': 15, 'Haight-Ashbury': 12}
}

# Constraints
constraints = {
    'Joshua': {'location': 'Embarcadero','start_time': '09:45', 'end_time': '18:00','required_time': 105},
    'Jeffrey': {'location': 'Bayview','start_time': '09:45', 'end_time': '20:15','required_time': 75},
    'Charles': {'location': 'Union Square','start_time': '10:45', 'end_time': '20:15','required_time': 120},
    'Joseph': {'location': 'Chinatown','start_time': '07:00', 'end_time': '15:30','required_time': 60},
    'Elizabeth': {'location': 'Sunset District','start_time': '09:00', 'end_time': '09:45','required_time': 45},
    'Matthew': {'location': 'Golden Gate Park','start_time': '11:00', 'end_time': '19:30','required_time': 45},
    'Carol': {'location': 'Financial District','start_time': '10:45', 'end_time': '11:15','required_time': 15},
    'Paul': {'location': 'Haight-Ashbury','start_time': '19:15', 'end_time': '20:30','required_time': 15},
    'Rebecca': {'location': 'Mission District','start_time': '17:00', 'end_time': '22:45','required_time': 45}
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