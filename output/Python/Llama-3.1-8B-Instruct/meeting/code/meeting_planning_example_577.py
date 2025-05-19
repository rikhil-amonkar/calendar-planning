import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Haight-Ashbury': {'Russian Hill': 17, 'Fisherman\'s Wharf': 23, 'Nob Hill': 15, 'Golden Gate Park': 7, 'Alamo Square': 5, 'Pacific Heights': 12},
    'Russian Hill': {'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'Nob Hill': 5, 'Golden Gate Park': 21, 'Alamo Square': 15, 'Pacific Heights': 7},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Russian Hill': 7, 'Nob Hill': 11, 'Golden Gate Park': 25, 'Alamo Square': 20, 'Pacific Heights': 12},
    'Nob Hill': {'Haight-Ashbury': 13, 'Russian Hill': 5, 'Fisherman\'s Wharf': 11, 'Golden Gate Park': 17, 'Alamo Square': 11, 'Pacific Heights': 8},
    'Golden Gate Park': {'Haight-Ashbury': 7, 'Russian Hill': 19, 'Fisherman\'s Wharf': 24, 'Nob Hill': 20, 'Alamo Square': 10, 'Pacific Heights': 16},
    'Alamo Square': {'Haight-Ashbury': 5, 'Russian Hill': 13, 'Fisherman\'s Wharf': 19, 'Nob Hill': 11, 'Golden Gate Park': 9, 'Pacific Heights': 10},
    'Pacific Heights': {'Haight-Ashbury': 11, 'Russian Hill': 7, 'Fisherman\'s Wharf': 13, 'Nob Hill': 8, 'Golden Gate Park': 15, 'Alamo Square': 10}
}

# Constraints
constraints = {
    'Stephanie': {'location': 'Russian Hill','start_time': '20:00', 'end_time': '20:45','required_time': 15},
    'Kevin': {'location': 'Fisherman\'s Wharf','start_time': '19:15', 'end_time': '21:45','required_time': 75},
    'Robert': {'location': 'Nob Hill','start_time': '07:45', 'end_time': '10:30','required_time': 90},
    'Steven': {'location': 'Golden Gate Park','start_time': '08:30', 'end_time': '17:00','required_time': 75},
    'Anthony': {'location': 'Alamo Square','start_time': '07:45', 'end_time': '19:45','required_time': 15},
    'Sandra': {'location': 'Pacific Heights','start_time': '14:45', 'end_time': '21:45','required_time': 45}
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