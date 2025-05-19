import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Presidio': {'Pacific Heights': 11, 'Golden Gate Park': 12, 'Fisherman\'s Wharf': 19, 'Marina District': 11, 'Alamo Square': 19, 'Sunset District': 15, 'Nob Hill': 18, 'North Beach': 18},
    'Pacific Heights': {'Presidio': 11, 'Golden Gate Park': 15, 'Fisherman\'s Wharf': 13, 'Marina District': 6, 'Alamo Square': 10, 'Sunset District': 21, 'Nob Hill': 8, 'North Beach': 9},
    'Golden Gate Park': {'Presidio': 11, 'Pacific Heights': 16, 'Fisherman\'s Wharf': 24, 'Marina District': 16, 'Alamo Square': 9, 'Sunset District': 10, 'Nob Hill': 20, 'North Beach': 23},
    'Fisherman\'s Wharf': {'Presidio': 17, 'Pacific Heights': 12, 'Golden Gate Park': 25, 'Marina District': 9, 'Alamo Square': 21, 'Sunset District': 27, 'Nob Hill': 11, 'North Beach': 6},
    'Marina District': {'Presidio': 10, 'Pacific Heights': 7, 'Golden Gate Park': 18, 'Fisherman\'s Wharf': 10, 'Alamo Square': 15, 'Sunset District': 19, 'Nob Hill': 12, 'North Beach': 11},
    'Alamo Square': {'Presidio': 17, 'Pacific Heights': 10, 'Golden Gate Park': 9, 'Fisherman\'s Wharf': 19, 'Marina District': 15, 'Sunset District': 16, 'Nob Hill': 11, 'North Beach': 15},
    'Sunset District': {'Presidio': 16, 'Pacific Heights': 21, 'Golden Gate Park': 11, 'Fisherman\'s Wharf': 29, 'Marina District': 21, 'Alamo Square': 17, 'Nob Hill': 27, 'North Beach': 28},
    'Nob Hill': {'Presidio': 17, 'Pacific Heights': 8, 'Golden Gate Park': 17, 'Fisherman\'s Wharf': 10, 'Marina District': 11, 'Alamo Square': 11, 'Sunset District': 24, 'North Beach': 8},
    'North Beach': {'Presidio': 17, 'Pacific Heights': 8, 'Golden Gate Park': 22, 'Fisherman\'s Wharf': 5, 'Marina District': 9, 'Alamo Square': 16, 'Sunset District': 27, 'Nob Hill': 7}
}

# Constraints
constraints = {
    'Kevin': {'location': 'Pacific Heights','start_time': '07:15', 'end_time': '08:45','required_time': 90},
    'Michelle': {'location': 'Golden Gate Park','start_time': '20:00', 'end_time': '21:00','required_time': 15},
    'Emily': {'location': 'Fisherman\'s Wharf','start_time': '16:15', 'end_time': '19:00','required_time': 30},
    'Mark': {'location': 'Marina District','start_time': '18:15', 'end_time': '20:45','required_time': 75},
    'Barbara': {'location': 'Alamo Square','start_time': '17:00', 'end_time': '19:00','required_time': 120},
    'Laura': {'location': 'Sunset District','start_time': '19:00', 'end_time': '21:15','required_time': 75},
    'Mary': {'location': 'Nob Hill','start_time': '17:30', 'end_time': '19:00','required_time': 45},
    'Helen': {'location': 'North Beach','start_time': '11:00', 'end_time': '12:15','required_time': 45}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Presidio', location)
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