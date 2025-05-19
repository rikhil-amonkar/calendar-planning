import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Golden Gate Park': {'Haight-Ashbury': 7, 'Fisherman\'s Wharf': 24, 'The Castro': 13, 'Chinatown': 23, 'Alamo Square': 10, 'North Beach': 24, 'Russian Hill': 19},
    'Haight-Ashbury': {'Golden Gate Park': 7, 'Fisherman\'s Wharf': 23, 'The Castro': 6, 'Chinatown': 19, 'Alamo Square': 5, 'North Beach': 19, 'Russian Hill': 17},
    'Fisherman\'s Wharf': {'Golden Gate Park': 25, 'Haight-Ashbury': 22, 'The Castro': 26, 'Chinatown': 12, 'Alamo Square': 20, 'North Beach': 6, 'Russian Hill': 7},
    'The Castro': {'Golden Gate Park': 11, 'Haight-Ashbury': 6, 'Fisherman\'s Wharf': 24, 'Chinatown': 20, 'Alamo Square': 8, 'North Beach': 20, 'Russian Hill': 18},
    'Chinatown': {'Golden Gate Park': 23, 'Haight-Ashbury': 19, 'Fisherman\'s Wharf': 8, 'The Castro': 22, 'Alamo Square': 17, 'North Beach': 3, 'Russian Hill': 7},
    'Alamo Square': {'Golden Gate Park': 9, 'Haight-Ashbury': 5, 'Fisherman\'s Wharf': 19, 'The Castro': 8, 'Chinatown': 16, 'North Beach': 15, 'Russian Hill': 13},
    'North Beach': {'Golden Gate Park': 22, 'Haight-Ashbury': 18, 'Fisherman\'s Wharf': 5, 'The Castro': 22, 'Chinatown': 6, 'Alamo Square': 16, 'Russian Hill': 4},
    'Russian Hill': {'Golden Gate Park': 21, 'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'The Castro': 21, 'Chinatown': 9, 'Alamo Square': 15, 'North Beach': 5}
}

# Constraints
constraints = {
    'Carol': {'location': 'Haight-Ashbury','start_time': '21:30', 'end_time': '22:30','required_time': 60},
    'Laura': {'location': 'Fisherman\'s Wharf','start_time': '11:45', 'end_time': '21:30','required_time': 60},
    'Karen': {'location': 'The Castro','start_time': '07:15', 'end_time': '14:00','required_time': 75},
    'Elizabeth': {'location': 'Chinatown','start_time': '12:15', 'end_time': '21:30','required_time': 75},
    'Deborah': {'location': 'Alamo Square','start_time': '12:00', 'end_time': '15:00','required_time': 105},
    'Jason': {'location': 'North Beach','start_time': '14:45', 'end_time': '19:00','required_time': 90},
    'Steven': {'location': 'Russian Hill','start_time': '14:45', 'end_time': '19:30','required_time': 120}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Golden Gate Park', location)
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