import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Embarcadero': {'Fisherman\'s Wharf': 6, 'Financial District': 5, 'Russian Hill': 8, 'Marina District': 12, 'Richmond District': 21, 'Pacific Heights': 11, 'Haight-Ashbury': 21, 'Presidio': 20, 'Nob Hill': 10, 'The Castro': 25},
    'Fisherman\'s Wharf': {'Embarcadero': 8, 'Financial District': 11, 'Russian Hill': 7, 'Marina District': 9, 'Richmond District': 18, 'Pacific Heights': 12, 'Haight-Ashbury': 22, 'Presidio': 17, 'Nob Hill': 11, 'The Castro': 27},
    'Financial District': {'Embarcadero': 4, 'Fisherman\'s Wharf': 10, 'Russian Hill': 11, 'Marina District': 15, 'Richmond District': 21, 'Pacific Heights': 13, 'Haight-Ashbury': 19, 'Presidio': 22, 'Nob Hill': 8, 'The Castro': 20},
    'Russian Hill': {'Embarcadero': 8, 'Fisherman\'s Wharf': 7, 'Financial District': 11, 'Marina District': 7, 'Richmond District': 14, 'Pacific Heights': 7, 'Haight-Ashbury': 17, 'Presidio': 14, 'Nob Hill': 5, 'The Castro': 21},
    'Marina District': {'Embarcadero': 14, 'Fisherman\'s Wharf': 10, 'Financial District': 17, 'Russian Hill': 8, 'Richmond District': 11, 'Pacific Heights': 7, 'Haight-Ashbury': 16, 'Presidio': 10, 'Nob Hill': 12, 'The Castro': 22},
    'Richmond District': {'Embarcadero': 19, 'Fisherman\'s Wharf': 18, 'Financial District': 22, 'Russian Hill': 13, 'Marina District': 9, 'Pacific Heights': 10, 'Haight-Ashbury': 10, 'Presidio': 7, 'Nob Hill': 17, 'The Castro': 16},
    'Pacific Heights': {'Embarcadero': 10, 'Fisherman\'s Wharf': 13, 'Financial District': 13, 'Russian Hill': 7, 'Marina District': 6, 'Richmond District': 12, 'Haight-Ashbury': 11, 'Presidio': 11, 'Nob Hill': 8, 'The Castro': 16},
    'Haight-Ashbury': {'Embarcadero': 20, 'Fisherman\'s Wharf': 23, 'Financial District': 21, 'Russian Hill': 17, 'Marina District': 17, 'Richmond District': 10, 'Pacific Heights': 12, 'Presidio': 15, 'Nob Hill': 15, 'The Castro': 6},
    'Presidio': {'Embarcadero': 20, 'Fisherman\'s Wharf': 19, 'Financial District': 23, 'Russian Hill': 14, 'Marina District': 11, 'Richmond District': 7, 'Pacific Heights': 11, 'Haight-Ashbury': 15, 'Nob Hill': 18, 'The Castro': 21},
    'Nob Hill': {'Embarcadero': 9, 'Fisherman\'s Wharf': 10, 'Financial District': 9, 'Russian Hill': 5, 'Marina District': 11, 'Richmond District': 14, 'Pacific Heights': 8, 'Haight-Ashbury': 13, 'Presidio': 17, 'The Castro': 17},
    'The Castro': {'Embarcadero': 22, 'Fisherman\'s Wharf': 24, 'Financial District': 21, 'Russian Hill': 18, 'Marina District': 21, 'Richmond District': 16, 'Pacific Heights': 16, 'Haight-Ashbury': 6, 'Presidio': 20, 'Nob Hill': 16}
}

# Constraints
constraints = {
    'Stephanie': {'location': 'Fisherman\'s Wharf','start_time': '15:30', 'end_time': '22:00','required_time': 30},
    'Lisa': {'location': 'Financial District','start_time': '10:45', 'end_time': '17:15','required_time': 15},
    'Melissa': {'location': 'Russian Hill','start_time': '17:00', 'end_time': '21:45','required_time': 120},
    'Betty': {'location': 'Marina District','start_time': '10:45', 'end_time': '14:15','required_time': 60},
    'Sarah': {'location': 'Richmond District','start_time': '16:15', 'end_time': '19:30','required_time': 105},
    'Daniel': {'location': 'Pacific Heights','start_time': '18:30', 'end_time': '21:45','required_time': 60},
    'Joshua': {'location': 'Haight-Ashbury','start_time': '09:00', 'end_time': '14:30','required_time': 15},
    'Joseph': {'location': 'Presidio','start_time': '07:00', 'end_time': '13:00','required_time': 45},
    'Andrew': {'location': 'Nob Hill','start_time': '19:45', 'end_time': '22:00','required_time': 105},
    'John': {'location': 'The Castro','start_time': '13:15', 'end_time': '20:45','required_time': 45}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(person, start_time, end_time, required_time):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=required_time)).time() <= datetime.strptime(end_time, '%H:%M').time()

def schedule_meeting(person, start_time, end_time, required_time, location):
    travel_time = calculate_travel_time('Embarcadero', location)
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