import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'The Castro': {'North Beach': 20, 'Golden Gate Park': 11, 'Embarcadero': 22, 'Haight-Ashbury': 6, 'Richmond District': 16, 'Nob Hill': 16, 'Marina District': 21, 'Presidio': 20, 'Union Square': 19, 'Financial District': 21},
    'North Beach': {'The Castro': 23, 'Golden Gate Park': 22, 'Embarcadero': 6, 'Haight-Ashbury': 18, 'Richmond District': 18, 'Nob Hill': 7, 'Marina District': 9, 'Presidio': 17, 'Union Square': 7, 'Financial District': 8},
    'Golden Gate Park': {'The Castro': 13, 'North Beach': 23, 'Embarcadero': 25, 'Haight-Ashbury': 7, 'Richmond District': 7, 'Nob Hill': 20, 'Marina District': 16, 'Presidio': 11, 'Union Square': 22, 'Financial District': 26},
    'Embarcadero': {'The Castro': 25, 'North Beach': 5, 'Golden Gate Park': 25, 'Haight-Ashbury': 21, 'Richmond District': 21, 'Nob Hill': 10, 'Marina District': 12, 'Presidio': 20, 'Union Square': 10, 'Financial District': 5},
    'Haight-Ashbury': {'The Castro': 6, 'North Beach': 19, 'Golden Gate Park': 7, 'Embarcadero': 20, 'Richmond District': 10, 'Nob Hill': 15, 'Marina District': 17, 'Presidio': 15, 'Union Square': 19, 'Financial District': 21},
    'Richmond District': {'The Castro': 16, 'North Beach': 17, 'Golden Gate Park': 9, 'Embarcadero': 19, 'Haight-Ashbury': 10, 'Nob Hill': 17, 'Marina District': 9, 'Presidio': 7, 'Union Square': 21, 'Financial District': 22},
    'Nob Hill': {'The Castro': 17, 'North Beach': 8, 'Golden Gate Park': 17, 'Embarcadero': 9, 'Haight-Ashbury': 13, 'Richmond District': 14, 'Marina District': 11, 'Presidio': 18, 'Union Square': 7, 'Financial District': 9},
    'Marina District': {'The Castro': 22, 'North Beach': 11, 'Golden Gate Park': 18, 'Embarcadero': 14, 'Haight-Ashbury': 16, 'Richmond District': 11, 'Nob Hill': 12, 'Presidio': 10, 'Union Square': 16, 'Financial District': 17},
    'Presidio': {'The Castro': 21, 'North Beach': 18, 'Golden Gate Park': 12, 'Embarcadero': 20, 'Haight-Ashbury': 15, 'Richmond District': 7, 'Nob Hill': 18, 'Marina District': 11, 'Union Square': 22, 'Financial District': 23},
    'Union Square': {'The Castro': 17, 'North Beach': 10, 'Golden Gate Park': 22, 'Embarcadero': 11, 'Haight-Ashbury': 18, 'Richmond District': 20, 'Nob Hill': 9, 'Marina District': 18, 'Presidio': 24, 'Financial District': 9},
    'Financial District': {'The Castro': 20, 'North Beach': 7, 'Golden Gate Park': 23, 'Embarcadero': 4, 'Haight-Ashbury': 19, 'Richmond District': 21, 'Nob Hill': 8, 'Marina District': 15, 'Presidio': 22, 'Union Square': 9}
}

# Constraints
constraints = {
    'Steven': {'location': 'North Beach','start_time': '17:30', 'end_time': '20:30','required_time': 15},
    'Sarah': {'location': 'Golden Gate Park','start_time': '17:00', 'end_time': '18:15','required_time': 75},
    'Brian': {'location': 'Embarcadero','start_time': '14:15', 'end_time': '16:00','required_time': 105},
    'Stephanie': {'location': 'Haight-Ashbury','start_time': '10:15', 'end_time': '12:15','required_time': 75},
    'Melissa': {'location': 'Richmond District','start_time': '14:00', 'end_time': '19:30','required_time': 30},
    'Nancy': {'location': 'Nob Hill','start_time': '08:15', 'end_time': '12:45','required_time': 90},
    'David': {'location': 'Marina District','start_time': '11:15', 'end_time': '13:15','required_time': 120},
    'James': {'location': 'Presidio','start_time': '15:00', 'end_time': '18:15','required_time': 120},
    'Elizabeth': {'location': 'Union Square','start_time': '11:30', 'end_time': '21:00','required_time': 60},
    'Robert': {'location': 'Financial District','start_time': '13:15', 'end_time': '15:15','required_time': 45}
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