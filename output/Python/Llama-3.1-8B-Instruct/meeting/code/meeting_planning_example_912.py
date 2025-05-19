import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Union Square': {'Presidio': 24, 'Alamo Square': 15, 'Marina District': 18, 'Financial District': 9, 'Nob Hill': 9, 'Sunset District': 27, 'Chinatown': 7, 'Russian Hill': 13, 'North Beach': 10, 'Haight-Ashbury': 18},
    'Presidio': {'Union Square': 22, 'Alamo Square': 19, 'Marina District': 11, 'Financial District': 23, 'Nob Hill': 18, 'Sunset District': 15, 'Chinatown': 21, 'Russian Hill': 14, 'North Beach': 18, 'Haight-Ashbury': 15},
    'Alamo Square': {'Union Square': 14, 'Presidio': 17, 'Marina District': 15, 'Financial District': 17, 'Nob Hill': 11, 'Sunset District': 16, 'Chinatown': 15, 'Russian Hill': 13, 'North Beach': 15, 'Haight-Ashbury': 5},
    'Marina District': {'Union Square': 16, 'Presidio': 10, 'Alamo Square': 15, 'Financial District': 17, 'Nob Hill': 12, 'Sunset District': 19, 'Chinatown': 15, 'Russian Hill': 8, 'North Beach': 11, 'Haight-Ashbury': 16},
    'Financial District': {'Union Square': 9, 'Presidio': 22, 'Alamo Square': 17, 'Marina District': 15, 'Nob Hill': 8, 'Sunset District': 30, 'Chinatown': 5, 'Russian Hill': 11, 'North Beach': 7, 'Haight-Ashbury': 19},
    'Nob Hill': {'Union Square': 7, 'Presidio': 17, 'Alamo Square': 11, 'Marina District': 11, 'Financial District': 9, 'Sunset District': 24, 'Chinatown': 6, 'Russian Hill': 5, 'North Beach': 8, 'Haight-Ashbury': 13},
    'Sunset District': {'Union Square': 30, 'Presidio': 16, 'Alamo Square': 17, 'Marina District': 21, 'Financial District': 30, 'Nob Hill': 27, 'Chinatown': 30, 'Russian Hill': 24, 'North Beach': 28, 'Haight-Ashbury': 15},
    'Chinatown': {'Union Square': 7, 'Presidio': 19, 'Alamo Square': 17, 'Marina District': 12, 'Financial District': 5, 'Nob Hill': 9, 'Sunset District': 29, 'Russian Hill': 7, 'North Beach': 3, 'Haight-Ashbury': 19},
    'Russian Hill': {'Union Square': 10, 'Presidio': 14, 'Alamo Square': 15, 'Marina District': 7, 'Financial District': 11, 'Nob Hill': 5, 'Sunset District': 23, 'Chinatown': 9, 'North Beach': 5, 'Haight-Ashbury': 17},
    'North Beach': {'Union Square': 7, 'Presidio': 17, 'Alamo Square': 16, 'Marina District': 9, 'Financial District': 8, 'Nob Hill': 7, 'Sunset District': 27, 'Chinatown': 6, 'Russian Hill': 4, 'Haight-Ashbury': 18},
    'Haight-Ashbury': {'Union Square': 19, 'Presidio': 15, 'Alamo Square': 5, 'Marina District': 17, 'Financial District': 21, 'Nob Hill': 15, 'Sunset District': 15, 'Chinatown': 19, 'Russian Hill': 17, 'North Beach': 19}
}

# Constraints
constraints = {
    'Kimberly': {'location': 'Presidio','start_time': '15:30', 'end_time': '16:00','required_time': 15},
    'Elizabeth': {'location': 'Alamo Square','start_time': '19:15', 'end_time': '20:15','required_time': 15},
    'Joshua': {'location': 'Marina District','start_time': '10:30', 'end_time': '14:15','required_time': 45},
    'Sandra': {'location': 'Financial District','start_time': '19:30', 'end_time': '20:15','required_time': 45},
    'Kenneth': {'location': 'Nob Hill','start_time': '12:45', 'end_time': '21:45','required_time': 30},
    'Betty': {'location': 'Sunset District','start_time': '14:00', 'end_time': '19:00','required_time': 60},
    'Deborah': {'location': 'Chinatown','start_time': '17:15', 'end_time': '20:30','required_time': 15},
    'Barbara': {'location': 'Russian Hill','start_time': '17:30', 'end_time': '21:15','required_time': 120},
    'Steven': {'location': 'North Beach','start_time': '17:45', 'end_time': '20:45','required_time': 90},
    'Daniel': {'location': 'Haight-Ashbury','start_time': '18:30', 'end_time': '18:45','required_time': 15}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Union Square', location)
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