import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Sunset District': 10,
        'Marina District': 16,
        'Financial District': 26,
        'Union Square': 22
    },
    'Haight-Ashbury': {
        'Golden Gate Park': 7,
        'Sunset District': 15,
        'Marina District': 17,
        'Financial District': 21,
        'Union Square': 17
    },
    'Sunset District': {
        'Golden Gate Park': 11,
        'Haight-Ashbury': 15,
        'Marina District': 21,
        'Financial District': 30,
        'Union Square': 30
    },
    'Marina District': {
        'Golden Gate Park': 18,
        'Haight-Ashbury': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Union Square': 16
    },
    'Financial District': {
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Sunset District': 31,
        'Marina District': 15,
        'Union Square': 9
    },
    'Union Square': {
        'Golden Gate Park': 22,
        'Haight-Ashbury': 18,
        'Sunset District': 26,
        'Marina District': 18,
        'Financial District': 9
    }
}

# Meeting constraints
constraints = {
    'Sarah': {'location': 'Haight-Ashbury','start_time': datetime(2024, 7, 26, 17, 0), 'end_time': datetime(2024, 7, 26, 21, 30),'min_time': 105},
    'Patricia': {'location': 'Sunset District','start_time': datetime(2024, 7, 26, 17, 0), 'end_time': datetime(2024, 7, 26, 19, 45),'min_time': 45},
    'Matthew': {'location': 'Marina District','start_time': datetime(2024, 7, 26, 9, 15), 'end_time': datetime(2024, 7, 26, 12, 0),'min_time': 15},
    'Joseph': {'location': 'Financial District','start_time': datetime(2024, 7, 26, 14, 15), 'end_time': datetime(2024, 7, 26, 20, 45),'min_time': 30},
    'Robert': {'location': 'Union Square','start_time': datetime(2024, 7, 26, 10, 15), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 15}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_meeting_possible(start_time, end_time, person):
    return start_time >= constraints[person]['start_time'] and end_time <= constraints[person]['end_time']

def is_time_enough(person, start_time, end_time):
    return end_time - start_time >= timedelta(minutes=constraints[person]['min_time'])

def find_meeting_schedule():
    schedule = []
    current_time = datetime(2024, 7, 26, 9, 0)
    current_location = 'Golden Gate Park'

    # Meet Matthew
    if is_meeting_possible(current_time, current_time + timedelta(minutes=calculate_travel_time(current_location, 'Marina District') + 15), 'Matthew'):
        schedule.append({'action':'meet', 'location': 'Marina District', 'person': 'Matthew','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Marina District') + 15)).strftime('%H:%M')})
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'Marina District') + 15)
        current_location = 'Marina District'
    else:
        current_time = constraints['Matthew']['start_time']
        schedule.append({'action':'wait', 'location': 'Marina District', 'person': 'Matthew','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=constraints['Matthew']['min_time'])).strftime('%H:%M')})
        current_time += timedelta(minutes=constraints['Matthew']['min_time'])

    # Meet Robert
    if is_meeting_possible(current_time, current_time + timedelta(minutes=calculate_travel_time(current_location, 'Union Square') + 15), 'Robert'):
        schedule.append({'action':'meet', 'location': 'Union Square', 'person': 'Robert','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Union Square') + 15)).strftime('%H:%M')})
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'Union Square') + 15)
        current_location = 'Union Square'
    else:
        while current_time < constraints['Robert']['start_time']:
            current_time += timedelta(minutes=1)
        schedule.append({'action':'wait', 'location': 'Union Square', 'person': 'Robert','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=constraints['Robert']['min_time'])).strftime('%H:%M')})
        current_time += timedelta(minutes=constraints['Robert']['min_time'])

    # Wait for Sarah
    while current_time < constraints['Sarah']['start_time']:
        current_time += timedelta(minutes=1)

    # Meet Sarah
    if is_meeting_possible(current_time, current_time + timedelta(minutes=calculate_travel_time(current_location, 'Haight-Ashbury') + 105), 'Sarah'):
        schedule.append({'action':'meet', 'location': 'Haight-Ashbury', 'person': 'Sarah','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Haight-Ashbury') + 105)).strftime('%H:%M')})
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'Haight-Ashbury') + 105)
        current_location = 'Haight-Ashbury'
    else:
        current_time = constraints['Sarah']['start_time']
        schedule.append({'action':'wait', 'location': 'Haight-Ashbury', 'person': 'Sarah','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=constraints['Sarah']['min_time'])).strftime('%H:%M')})
        current_time += timedelta(minutes=constraints['Sarah']['min_time'])

    # Meet Patricia
    if is_meeting_possible(current_time, current_time + timedelta(minutes=calculate_travel_time(current_location, 'Sunset District') + 45), 'Patricia'):
        schedule.append({'action':'meet', 'location': 'Sunset District', 'person': 'Patricia','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Sunset District') + 45)).strftime('%H:%M')})
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'Sunset District') + 45)
        current_location = 'Sunset District'
    else:
        current_time = constraints['Patricia']['start_time']
        schedule.append({'action':'wait', 'location': 'Sunset District', 'person': 'Patricia','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=constraints['Patricia']['min_time'])).strftime('%H:%M')})
        current_time += timedelta(minutes=constraints['Patricia']['min_time'])

    # Wait for Joseph
    while current_time < constraints['Joseph']['start_time']:
        current_time += timedelta(minutes=1)

    # Meet Joseph
    if is_meeting_possible(current_time, current_time + timedelta(minutes=calculate_travel_time(current_location, 'Financial District') + 30), 'Joseph'):
        schedule.append({'action':'meet', 'location': 'Financial District', 'person': 'Joseph','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Financial District') + 30)).strftime('%H:%M')})
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'Financial District') + 30)
        current_location = 'Financial District'
    else:
        current_time = constraints['Joseph']['start_time']
        schedule.append({'action':'wait', 'location': 'Financial District', 'person': 'Joseph','start_time': current_time.strftime('%H:%M'), 'end_time': (current_time + timedelta(minutes=constraints['Joseph']['min_time'])).strftime('%H:%M')})
        current_time += timedelta(minutes=constraints['Joseph']['min_time'])

    return schedule

def main():
    schedule = find_meeting_schedule()
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == "__main__":
    main()