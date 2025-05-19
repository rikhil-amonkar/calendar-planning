import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Financial District': {'Fisherman\'s Wharf': 10, 'Pacific Heights': 13, 'Mission District': 17},
    'Fisherman\'s Wharf': {'Financial District': 11, 'Pacific Heights': 12, 'Mission District': 22},
    'Pacific Heights': {'Financial District': 13, 'Fisherman\'s Wharf': 13, 'Mission District': 15},
    'Mission District': {'Financial District': 17, 'Fisherman\'s Wharf': 22, 'Pacific Heights': 16}
}

# Constraints
constraints = {
    'David': {'location': 'Fisherman\'s Wharf','start_time': '10:45', 'end_time': '15:30','required_time': 15},
    'Timothy': {'location': 'Pacific Heights','start_time': '09:00', 'end_time': '15:30','required_time': 75},
    'Robert': {'location': 'Mission District','start_time': '12:15', 'end_time': '19:45','required_time': 90}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Financial District', location)
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