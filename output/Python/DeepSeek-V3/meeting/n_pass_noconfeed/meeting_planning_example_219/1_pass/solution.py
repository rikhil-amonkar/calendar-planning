import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times in minutes (from: {to: time})
    travel_times = {
        'The Castro': {'Alamo Square': 8, 'Union Square': 19, 'Chinatown': 20},
        'Alamo Square': {'The Castro': 8, 'Union Square': 14, 'Chinatown': 16},
        'Union Square': {'The Castro': 19, 'Alamo Square': 15, 'Chinatown': 7},
        'Chinatown': {'The Castro': 22, 'Alamo Square': 17, 'Union Square': 7}
    }

    # Constraints
    start_location = 'The Castro'
    start_time = '9:00'
    emily = {'location': 'Alamo Square', 'start': '11:45', 'end': '15:15', 'min_duration': 105}
    barbara = {'location': 'Union Square', 'start': '16:45', 'end': '18:15', 'min_duration': 60}
    william = {'location': 'Chinatown', 'start': '17:15', 'end': '19:00', 'min_duration': 105}

    # Convert all times to minutes
    current_time = time_to_minutes(start_time)
    emily['start'] = time_to_minutes(emily['start'])
    emily['end'] = time_to_minutes(emily['end'])
    barbara['start'] = time_to_minutes(barbara['start'])
    barbara['end'] = time_to_minutes(barbara['end'])
    william['start'] = time_to_minutes(william['start'])
    william['end'] = time_to_minutes(william['end'])

    # Possible meeting orders (permutations of Emily, Barbara, William)
    people = ['Emily', 'Barbara', 'William']
    best_schedule = None
    best_meetings = 0

    for order in permutations(people):
        schedule = []
        current_loc = start_location
        current_time = time_to_minutes(start_time)
        meetings = 0
        valid = True

        for person in order:
            if person == 'Emily':
                p = emily
            elif person == 'Barbara':
                p = barbara
            else:
                p = william

            # Travel to person's location
            travel_time = travel_times[current_loc][p['location']]
            arrival_time = current_time + travel_time

            # Check if we can meet the person
            meeting_start = max(arrival_time, p['start'])
            meeting_end = meeting_start + p['min_duration']

            if meeting_end > p['end']:
                valid = False
                break

            # Add meeting to schedule
            schedule.append({
                'action': 'meet',
                'location': p['location'],
                'person': person,
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings += 1

            # Update current time and location
            current_time = meeting_end
            current_loc = p['location']

        if valid and meetings > best_meetings:
            best_meetings = meetings
            best_schedule = schedule

    # If no valid schedule found, try with fewer meetings
    if best_schedule is None:
        for order in permutations(people, 2):
            schedule = []
            current_loc = start_location
            current_time = time_to_minutes(start_time)
            meetings = 0
            valid = True

            for person in order:
                if person == 'Emily':
                    p = emily
                elif person == 'Barbara':
                    p = barbara
                else:
                    p = william

                travel_time = travel_times[current_loc][p['location']]
                arrival_time = current_time + travel_time

                meeting_start = max(arrival_time, p['start'])
                meeting_end = meeting_start + p['min_duration']

                if meeting_end > p['end']:
                    valid = False
                    break

                schedule.append({
                    'action': 'meet',
                    'location': p['location'],
                    'person': person,
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1

                current_time = meeting_end
                current_loc = p['location']

            if valid and meetings > best_meetings:
                best_meetings = meetings
                best_schedule = schedule

    return {'itinerary': best_schedule} if best_schedule else {'itinerary': []}

result = calculate_schedule()
print(json.dumps(result, indent=2))