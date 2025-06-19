import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    'Marina District to Embarcadero': 14,
    'Marina District to Bayview': 27,
    'Marina District to Union Square': 16,
    'Marina District to Chinatown': 15,
    'Marina District to Sunset District': 19,
    'Marina District to Golden Gate Park': 18,
    'Marina District to Financial District': 17,
    'Marina District to Haight-Ashbury': 16,
    'Marina District to Mission District': 20,
    'Embarcadero to Marina District': 12,
    'Embarcadero to Bayview': 21,
    'Embarcadero to Union Square': 10,
    'Embarcadero to Chinatown': 7,
    'Embarcadero to Sunset District': 30,
    'Embarcadero to Golden Gate Park': 25,
    'Embarcadero to Financial District': 5,
    'Embarcadero to Haight-Ashbury': 21,
    'Embarcadero to Mission District': 20,
    'Bayview to Marina District': 27,
    'Bayview to Embarcadero': 19,
    'Bayview to Union Square': 18,
    'Bayview to Chinatown': 19,
    'Bayview to Sunset District': 23,
    'Bayview to Golden Gate Park': 22,
    'Bayview to Financial District': 19,
    'Bayview to Haight-Ashbury': 19,
    'Bayview to Mission District': 13,
    'Union Square to Marina District': 18,
    'Union Square to Embarcadero': 11,
    'Union Square to Bayview': 15,
    'Union Square to Chinatown': 7,
    'Union Square to Sunset District': 27,
    'Union Square to Golden Gate Park': 22,
    'Union Square to Financial District': 9,
    'Union Square to Haight-Ashbury': 18,
    'Union Square to Mission District': 14,
    'Chinatown to Marina District': 12,
    'Chinatown to Embarcadero': 5,
    'Chinatown to Bayview': 20,
    'Chinatown to Union Square': 7,
    'Chinatown to Sunset District': 29,
    'Chinatown to Golden Gate Park': 23,
    'Chinatown to Financial District': 5,
    'Chinatown to Haight-Ashbury': 19,
    'Chinatown to Mission District': 17,
    'Sunset District to Marina District': 21,
    'Sunset District to Embarcadero': 30,
    'Sunset District to Bayview': 22,
    'Sunset District to Union Square': 30,
    'Sunset District to Chinatown': 30,
    'Sunset District to Golden Gate Park': 11,
    'Sunset District to Financial District': 30,
    'Sunset District to Haight-Ashbury': 15,
    'Sunset District to Mission District': 25,
    'Golden Gate Park to Marina District': 16,
    'Golden Gate Park to Embarcadero': 25,
    'Golden Gate Park to Bayview': 23,
    'Golden Gate Park to Union Square': 22,
    'Golden Gate Park to Chinatown': 23,
    'Golden Gate Park to Sunset District': 10,
    'Golden Gate Park to Financial District': 26,
    'Golden Gate Park to Haight-Ashbury': 7,
    'Golden Gate Park to Mission District': 17,
    'Financial District to Marina District': 15,
    'Financial District to Embarcadero': 4,
    'Financial District to Bayview': 19,
    'Financial District to Union Square': 9,
    'Financial District to Chinatown': 5,
    'Financial District to Sunset District': 30,
    'Financial District to Golden Gate Park': 23,
    'Financial District to Haight-Ashbury': 19,
    'Financial District to Mission District': 17,
    'Haight-Ashbury to Marina District': 17,
    'Haight-Ashbury to Embarcadero': 20,
    'Haight-Ashbury to Bayview': 18,
    'Haight-Ashbury to Union Square': 19,
    'Haight-Ashbury to Chinatown': 19,
    'Haight-Ashbury to Sunset District': 15,
    'Haight-Ashbury to Golden Gate Park': 7,
    'Haight-Ashbury to Financial District': 21,
    'Haight-Ashbury to Mission District': 11,
    'Mission District to Marina District': 19,
    'Mission District to Embarcadero': 19,
    'Mission District to Bayview': 14,
    'Mission District to Union Square': 15,
    'Mission District to Chinatown': 16,
    'Mission District to Sunset District': 24,
    'Mission District to Golden Gate Park': 17,
    'Mission District to Financial District': 15,
    'Mission District to Haight-Ashbury': 12
}

# Meeting constraints
constraints = {
    'Joshua': {'location': 'Embarcadero','start_time': '09:45', 'end_time': '18:00', 'duration': 105},
    'Jeffrey': {'location': 'Bayview','start_time': '09:45', 'end_time': '20:15', 'duration': 75},
    'Charles': {'location': 'Union Square','start_time': '10:45', 'end_time': '20:15', 'duration': 120},
    'Joseph': {'location': 'Chinatown','start_time': '07:00', 'end_time': '15:30', 'duration': 60},
    'Elizabeth': {'location': 'Sunset District','start_time': '09:00', 'end_time': '09:45', 'duration': 45},
    'Matthew': {'location': 'Golden Gate Park','start_time': '11:00', 'end_time': '19:30', 'duration': 45},
    'Carol': {'location': 'Financial District','start_time': '10:45', 'end_time': '11:15', 'duration': 15},
    'Paul': {'location': 'Haight-Ashbury','start_time': '19:15', 'end_time': '20:30', 'duration': 15},
    'Rebecca': {'location': 'Mission District','start_time': '17:00', 'end_time': '20:45', 'duration': 45}
}

def calculate_travel_time(start_location, end_location):
    return travel_times[f'{start_location} to {end_location}']

def is_valid_schedule(schedule):
    for person in constraints:
        if person not in schedule:
            return False
        start_time = schedule[person]['start_time']
        end_time = schedule[person]['end_time']
        duration = schedule[person]['duration']
        if start_time < constraints[person]['start_time'] or end_time > constraints[person]['end_time']:
            return False
        if datetime.strptime(end_time, '%H:%M') - datetime.strptime(start_time, '%H:%M') < timedelta(minutes=duration):
            return False
    return True

def find_optimal_schedule():
    # Initialize schedule
    schedule = {}
    for person in constraints:
        schedule[person] = {'start_time': constraints[person]['start_time'], 'end_time': constraints[person]['end_time'], 'duration': constraints[person]['duration']}

    # Sort locations by distance from Marina District
    locations = list(constraints.values())
    locations.sort(key=lambda x: calculate_travel_time('Marina District', x['location']))

    # Initialize current time and current location
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Marina District'

    # Iterate over locations
    for location in locations:
        # Find person with matching location
        person = next((p for p in constraints if constraints[p]['location'] == location['location']), None)
        if person is None:
            continue

        # Calculate travel time to location
        travel_time = calculate_travel_time(current_location, location['location'])
        # Update current time and location
        current_time += timedelta(minutes=travel_time)
        current_location = location['location']

        # Find earliest start time for person
        earliest_start_time = current_time.strftime('%H:%M')
        # Update schedule
        schedule[person]['start_time'] = earliest_start_time
        schedule[person]['end_time'] = (current_time + timedelta(minutes=constraints[person]['duration'])).strftime('%H:%M')
        # Update current time
        current_time += timedelta(minutes=constraints[person]['duration'])

    # Check if schedule is valid
    if is_valid_schedule(schedule):
        return schedule
    else:
        return None

def generate_itinerary(schedule):
    itinerary = []
    for person in schedule:
        start_time = schedule[person]['start_time']
        end_time = schedule[person]['end_time']
        location = constraints[person]['location']
        action ='meet'
        itinerary.append({'action': action, 'location': location, 'person': person,'start_time': start_time, 'end_time': end_time})

        # Add travel times to itinerary
        for other_person in constraints:
            if other_person!= person and constraints[other_person]['location']!= location:
                other_start_time = datetime.strptime(schedule[other_person]['start_time'], '%H:%M')
                if other_start_time < datetime.strptime(start_time, '%H:%M'):
                    travel_time = calculate_travel_time(location, constraints[other_person]['location'])
                    itinerary.append({'action': 'travel', 'location': location, 'destination': constraints[other_person]['location'],'start_time': start_time, 'end_time': (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=travel_time)).strftime('%H:%M')})

        # Add travel time from last meeting to current meeting
        if itinerary:
            last_meeting = itinerary[-1]
            if last_meeting['action'] =='meet':
                last_meeting_end_time = datetime.strptime(last_meeting['end_time'], '%H:%M')
                travel_time = calculate_travel_time(last_meeting['location'], location)
                itinerary.append({'action': 'travel', 'location': last_meeting['location'], 'destination': location,'start_time': last_meeting_end_time.strftime('%H:%M'), 'end_time': (last_meeting_end_time + timedelta(minutes=travel_time)).strftime('%H:%M')})

    return itinerary

def main():
    optimal_schedule = find_optimal_schedule()
    if optimal_schedule is not None:
        itinerary = generate_itinerary(optimal_schedule)
        print(json.dumps({'itinerary': itinerary}, indent=4))
    else:
        print('No valid schedule found')

if __name__ == '__main__':
    main()