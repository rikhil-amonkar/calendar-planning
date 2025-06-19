import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Golden Gate Park': 25,
        'Nob Hill': 11,
        'Marina District': 9,
        'Embarcadero': 8
    },
    'Bayview': {
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22,
        'Nob Hill': 20,
        'Marina District': 25,
        'Embarcadero': 19
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Nob Hill': 20,
        'Marina District': 16,
        'Embarcadero': 25
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'Bayview': 19,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Embarcadero': 9
    },
    'Marina District': {
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Golden Gate Park': 18,
        'Nob Hill': 12,
        'Embarcadero': 14
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Golden Gate Park': 25,
        'Nob Hill': 10,
        'Marina District': 12
    }
}

# Meeting constraints
constraints = {
    'Thomas': {'location': 'Bayview','start_time': '15:30', 'end_time': '18:30','min_meeting_time': 120},
    'Stephanie': {'location': 'Golden Gate Park','start_time': '18:30', 'end_time': '21:45','min_meeting_time': 30},
    'Laura': {'location': 'Nob Hill','start_time': '08:45', 'end_time': '16:15','min_meeting_time': 30},
    'Betty': {'location': 'Marina District','start_time': '18:45', 'end_time': '21:45','min_meeting_time': 45},
    'Patricia': {'location': 'Embarcadero','start_time': '17:30', 'end_time': '22:00','min_meeting_time': 45}
}

def calculate_arrival_time(departure_time, travel_time):
    departure_time = datetime.strptime(departure_time, '%H:%M')
    travel_time = min(travel_time, (datetime.strptime('23:59', '%H:%M') - departure_time).total_seconds() / 60)
    arrival_time = departure_time + timedelta(minutes=travel_time)
    return arrival_time.strftime('%H:%M')

def is_valid_meeting(schedule, current_time, current_location, person):
    for meeting in schedule:
        if meeting['start_time'] <= current_time <= meeting['end_time'] and meeting['location'] == current_location and meeting['person'] == person:
            return False
    return True

def compute_meeting_schedule():
    schedule = []
    current_time = '09:00'
    current_location = 'Fisherman\'s Wharf'

    for person, constraint in constraints.items():
        if current_time < constraint['start_time']:
            current_time = constraint['start_time']
        travel_time = travel_distances[current_location][constraint['location']]
        arrival_time = calculate_arrival_time(current_time, travel_time)
        if arrival_time < constraint['start_time']:
            continue
        meeting_time = max(constraint['min_meeting_time'], 60)  # Ensure meeting time is at least 60 minutes
        end_time = calculate_arrival_time(arrival_time, meeting_time)
        if end_time > constraint['end_time']:
            continue
        if is_valid_meeting(schedule, arrival_time, current_location, person):
            schedule.append({
                'action':'meet',
                'location': constraint['location'],
                'person': person,
               'start_time': arrival_time,
                'end_time': end_time
            })
        current_location = constraint['location']
        current_time = end_time

    return schedule

def main():
    schedule = compute_meeting_schedule()
    print('SOLUTION:')
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == '__main__':
    main()