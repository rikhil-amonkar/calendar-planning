import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Castro': {
        'Bayview': 19,
        'Pacific Heights': 16,
        'Alamo Square': 8,
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 11
    },
    'Bayview': {
        'Castro': 20,
        'Pacific Heights': 23,
        'Alamo Square': 16,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'Castro': 16,
        'Bayview': 22,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15
    },
    'Alamo Square': {
        'Castro': 8,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 9
    },
    'Fisherman\'s Wharf': {
        'Castro': 26,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Alamo Square': 20,
        'Golden Gate Park': 25
    },
    'Golden Gate Park': {
        'Castro': 13,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 24
    }
}

# Define meeting constraints
constraints = {
    'Rebecca': {'location': 'Bayview','start_time': '09:00', 'end_time': '12:45', 'duration': 90},
    'Amanda': {'location': 'Pacific Heights','start_time': '18:30', 'end_time': '21:45', 'duration': 90},
    'James': {'location': 'Alamo Square','start_time': '09:45', 'end_time': '21:15', 'duration': 90},
    'Sarah': {'location': 'Fisherman\'s Wharf','start_time': '08:00', 'end_time': '21:30', 'duration': 90},
    'Melissa': {'location': 'Golden Gate Park','start_time': '09:00', 'end_time': '18:45', 'duration': 90}
}

# Function to calculate travel time
def calculate_travel_time(location1, location2):
    return travel_distances[location1][location2]

# Function to check if meeting is possible
def is_meeting_possible(location1, location2, start_time1, end_time1, start_time2, end_time2):
    travel_time = calculate_travel_time(location1, location2)
    start_time2 = max(start_time2, start_time1 + timedelta(minutes=travel_time))
    end_time2 = min(end_time2, end_time1 + timedelta(minutes=travel_time))
    return end_time2 - start_time2 >= timedelta(minutes=constraints[location2]['duration']).total_seconds() / 60

# Function to generate optimal meeting schedule
def generate_meeting_schedule():
    schedule = []
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('18:00', '%H:%M')
    locations = list(constraints.keys())
    while start_time < end_time:
        for i in range(len(locations)):
            for j in range(i+1, len(locations)):
                location1 = locations[i]
                location2 = locations[j]
                if is_meeting_possible(location1, location2, start_time.strftime('%H:%M'), end_time.strftime('%H:%M'), constraints[location1]['start_time'], constraints[location1]['end_time']) and \
                   is_meeting_possible(location2, location1, start_time.strftime('%H:%M'), end_time.strftime('%H:%M'), constraints[location2]['start_time'], constraints[location2]['end_time']):
                    schedule.append({'action':'meet', 'location': location1, 'person': location2,'start_time': start_time.strftime('%H:%M'), 'end_time': (start_time + timedelta(minutes=constraints[location2]['duration'])).strftime('%H:%M')})
                    start_time += timedelta(minutes=constraints[location2]['duration'])
                    break
            else:
                continue
            break
    return schedule

# Generate optimal meeting schedule
schedule = generate_meeting_schedule()

# Output schedule as JSON
print(json.dumps({'itinerary': schedule}, indent=4))