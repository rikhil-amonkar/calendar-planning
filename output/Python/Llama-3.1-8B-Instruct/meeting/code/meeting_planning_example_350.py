import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Bayview': {'Pacific Heights': 23, 'Mission District': 13, 'Haight-Ashbury': 19, 'Financial District': 19},
    'Pacific Heights': {'Bayview': 22, 'Mission District': 15, 'Haight-Ashbury': 11, 'Financial District': 13},
    'Mission District': {'Bayview': 15, 'Pacific Heights': 16, 'Haight-Ashbury': 12, 'Financial District': 17},
    'Haight-Ashbury': {'Bayview': 18, 'Pacific Heights': 12, 'Mission District': 11, 'Financial District': 21},
    'Financial District': {'Bayview': 19, 'Pacific Heights': 13, 'Mission District': 17, 'Haight-Ashbury': 19}
}

# Constraints
constraints = {
    'Mary': {'location': 'Pacific Heights','start_time': '10:00', 'end_time': '19:00','required_time': 45},
    'Lisa': {'location': 'Mission District','start_time': '20:30', 'end_time': '22:00','required_time': 75},
    'Betty': {'location': 'Haight-Ashbury','start_time': '07:15', 'end_time': '17:15','required_time': 90},
    'Charles': {'location': 'Financial District','start_time': '11:15', 'end_time': '15:00','required_time': 120}
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