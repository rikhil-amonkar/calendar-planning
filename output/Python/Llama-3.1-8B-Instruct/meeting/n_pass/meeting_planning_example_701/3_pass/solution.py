import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Mission District': {
        'The Castro': 7,
        'Nob Hill': 12,
        'Presidio': 25,
        'Marina District': 19,
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'Chinatown': 16,
        'Richmond District': 20
    },
    'The Castro': {
        'Mission District': 7,
        'Nob Hill': 16,
        'Presidio': 20,
        'Marina District': 21,
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Chinatown': 22,
        'Richmond District': 16
    },
    'Nob Hill': {
        'Mission District': 13,
        'The Castro': 17,
        'Presidio': 17,
        'Marina District': 11,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Chinatown': 6,
        'Richmond District': 14
    },
    'Presidio': {
        'Mission District': 26,
        'The Castro': 21,
        'Nob Hill': 18,
        'Marina District': 11,
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7
    },
    'Marina District': {
        'Mission District': 20,
        'The Castro': 22,
        'Nob Hill': 12,
        'Presidio': 10,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Chinatown': 15,
        'Richmond District': 11
    },
    'Pacific Heights': {
        'Mission District': 15,
        'The Castro': 16,
        'Nob Hill': 8,
        'Presidio': 11,
        'Marina District': 6,
        'Golden Gate Park': 15,
        'Chinatown': 11,
        'Richmond District': 12
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'The Castro': 13,
        'Nob Hill': 20,
        'Presidio': 11,
        'Marina District': 16,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Richmond District': 7
    },
    'Chinatown': {
        'Mission District': 16,
        'The Castro': 22,
        'Nob Hill': 9,
        'Presidio': 19,
        'Marina District': 12,
        'Pacific Heights': 10,
        'Golden Gate Park': 23,
        'Richmond District': 20
    },
    'Richmond District': {
        'Mission District': 20,
        'The Castro': 16,
        'Nob Hill': 17,
        'Presidio': 7,
        'Marina District': 9,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Chinatown': 20
    }
}

# Constraints
constraints = [
    {'name': 'Lisa', 'location': 'The Castro','start_time': '09:07', 'end_time': '19:15', 'duration': 120},
    {'name': 'Daniel', 'location': 'Nob Hill','start_time': '8:15', 'end_time': '11:00', 'duration': 15},
    {'name': 'Elizabeth', 'location': 'Presidio','start_time': '08:49', 'end_time': '21:15', 'duration': 45},
    {'name': 'Steven', 'location': 'Marina District','start_time': '16:30', 'end_time': '20:45', 'duration': 90},
    {'name': 'Timothy', 'location': 'Pacific Heights','start_time': '12:00', 'end_time': '18:00', 'duration': 90},
    {'name': 'Ashley', 'location': 'Golden Gate Park','start_time': '12:21', 'end_time': '20:45', 'duration': 60},
    {'name': 'Kevin', 'location': 'Chinatown','start_time': '12:00', 'end_time': '19:00', 'duration': 30},
    {'name': 'Betty', 'location': 'Richmond District','start_time': '12:43', 'end_time': '13:15', 'duration': 30}
]

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def schedule_meetings(constraints):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    start_location = 'Mission District'
    for constraint in constraints:
        end_location = constraint['location']
        travel_time = calculate_travel_time(start_location, end_location)
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time < datetime.strptime(constraint['start_time'], '%H:%M'):
            # Wait until the start time
            wait_time = datetime.strptime(constraint['start_time'], '%H:%M') - arrival_time
            schedule.append({'action': 'wait', 'location': end_location, 'person': constraint['name'],'start_time': arrival_time.strftime('%H:%M'), 'end_time': (arrival_time + wait_time).strftime('%H:%M')})
            current_time = (arrival_time + wait_time)
        else:
            schedule.append({'action':'meet', 'location': end_location, 'person': constraint['name'],'start_time': constraint['start_time'], 'end_time': (datetime.strptime(constraint['start_time'], '%H:%M') + timedelta(minutes=constraint['duration'])).strftime('%H:%M')})
            current_time = datetime.strptime(constraint['start_time'], '%H:%M') + timedelta(minutes=constraint['duration'])
        # Calculate the time to travel back to the starting location
        travel_time = calculate_travel_time(end_location, start_location)
        current_time += timedelta(minutes=travel_time)
        start_location = end_location
    return schedule

def main():
    schedule = schedule_meetings(constraints)
    itinerary = []
    for item in schedule:
        if item['action'] == 'wait':
            item['action'] = 'wait at'+ item['location']
        itinerary.append({
            'action': item['action'],
            'location': item['location'],
            'person': item['person'],
         'start_time': item['start_time'],
            'end_time': item['end_time']
        })
    output = {'itinerary': itinerary}
    print(json.dumps(output, indent=4))

if __name__ == '__main__':
    main()