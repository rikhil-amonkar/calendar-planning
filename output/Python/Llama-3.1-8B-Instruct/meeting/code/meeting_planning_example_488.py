import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Pacific Heights': {'Nob Hill': 8, 'Russian Hill': 7, 'The Castro': 16, 'Sunset District': 21, 'Haight-Ashbury': 11},
    'Nob Hill': {'Pacific Heights': 8, 'Russian Hill': 5, 'The Castro': 17, 'Sunset District': 25, 'Haight-Ashbury': 13},
    'Russian Hill': {'Pacific Heights': 7, 'Nob Hill': 5, 'The Castro': 21, 'Sunset District': 23, 'Haight-Ashbury': 17},
    'The Castro': {'Pacific Heights': 16, 'Nob Hill': 16, 'Russian Hill': 18, 'Sunset District': 17, 'Haight-Ashbury': 6},
    'Sunset District': {'Pacific Heights': 21, 'Nob Hill': 27, 'Russian Hill': 24, 'The Castro': 17, 'Haight-Ashbury': 15},
    'Haight-Ashbury': {'Pacific Heights': 12, 'Nob Hill': 15, 'Russian Hill': 17, 'The Castro': 6, 'Sunset District': 15}
}

# Constraints
constraints = {
    'Ronald': {'location': 'Nob Hill','start_time': '10:00', 'end_time': '17:00','required_time': 105},
    'Sarah': {'location': 'Russian Hill','start_time': '07:15', 'end_time': '09:30','required_time': 45},
    'Helen': {'location': 'The Castro','start_time': '13:30', 'end_time': '17:00','required_time': 120},
    'Joshua': {'location': 'Sunset District','start_time': '14:15', 'end_time': '20:30','required_time': 90},
    'Margaret': {'location': 'Haight-Ashbury','start_time': '10:15', 'end_time': '22:00','required_time': 60}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Pacific Heights', location)
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