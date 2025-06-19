import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    'Bayview': {
        'Russian Hill': 23,
        'Alamo Square': 16,
        'North Beach': 21,
        'Financial District': 19
    },
    'Russian Hill': {
        'Bayview': 23,
        'Alamo Square': 15,
        'North Beach': 5,
        'Financial District': 11
    },
    'Alamo Square': {
        'Bayview': 16,
        'Russian Hill': 13,
        'North Beach': 15,
        'Financial District': 17
    },
    'North Beach': {
        'Bayview': 22,
        'Russian Hill': 4,
        'Alamo Square': 16,
        'Financial District': 8
    },
    'Financial District': {
        'Bayview': 19,
        'Russian Hill': 10,
        'Alamo Square': 17,
        'North Beach': 7
    }
}

# Meeting constraints
constraints = {
    'Joseph': {
        'location': 'Russian Hill',
       'start_time': '08:30',
        'end_time': '19:15',
       'min_meeting_time': 60
    },
    'Nancy': {
        'location': 'Alamo Square',
       'start_time': '11:00',
        'end_time': '16:00',
       'min_meeting_time': 90
    },
    'Jason': {
        'location': 'North Beach',
       'start_time': '16:45',
        'end_time': '21:45',
       'min_meeting_time': 15
    },
    'Jeffrey': {
        'location': 'Financial District',
       'start_time': '10:30',
        'end_time': '15:45',
       'min_meeting_time': 45
    }
}

def calculate_travel_time(start_location, end_location):
    try:
        return travel_distances[start_location][end_location]
    except KeyError:
        # If a location is not found, return a default travel time of 30 minutes
        return 30

def is_valid_meeting(start_time, end_time, meeting_time):
    return end_time - start_time >= timedelta(minutes=meeting_time)

def find_optimal_meeting_schedule():
    # Initialize schedule
    schedule = []

    # Start at Bayview at 09:00
    current_location = 'Bayview'
    current_time = datetime.strptime('09:00', '%H:%M')

    # Meet Joseph
    joseph_start_time = datetime.strptime(constraints['Joseph']['start_time'], '%H:%M')
    joseph_end_time = datetime.strptime(constraints['Joseph']['end_time'], '%H:%M')
    if is_valid_meeting(current_time, joseph_start_time, constraints['Joseph']['min_meeting_time']):
        schedule.append({
            'action':'meet',
            'location': 'Russian Hill',
            'person': 'Joseph',
           'start_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Russian Hill'))).strftime('%H:%M'),
            'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Russian Hill') + constraints['Joseph']['min_meeting_time'])).strftime('%H:%M')
        })
        current_location = 'Russian Hill'
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'Russian Hill') + constraints['Joseph']['min_meeting_time'])

    # Meet Nancy
    nancy_start_time = datetime.strptime(constraints['Nancy']['start_time'], '%H:%M')
    nancy_end_time = datetime.strptime(constraints['Nancy']['end_time'], '%H:%M')
    if is_valid_meeting(current_time, nancy_start_time, constraints['Nancy']['min_meeting_time']) and current_time < nancy_start_time:
        # Check if Nancy's meeting time conflicts with her availability
        if current_time + timedelta(minutes=calculate_travel_time(current_location, 'Alamo Square') + constraints['Nancy']['min_meeting_time']) <= nancy_start_time:
            schedule.append({
                'action':'meet',
                'location': 'Alamo Square',
                'person': 'Nancy',
               'start_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Alamo Square'))).strftime('%H:%M'),
                'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Alamo Square') + constraints['Nancy']['min_meeting_time'])).strftime('%H:%M')
            })
            current_location = 'Alamo Square'
            current_time += timedelta(minutes=calculate_travel_time(current_location, 'Alamo Square') + constraints['Nancy']['min_meeting_time'])

    # Meet Jeffrey
    jeffrey_start_time = datetime.strptime(constraints['Jeffrey']['start_time'], '%H:%M')
    jeffrey_end_time = datetime.strptime(constraints['Jeffrey']['end_time'], '%H:%M')
    if is_valid_meeting(current_time, jeffrey_start_time, constraints['Jeffrey']['min_meeting_time']):
        schedule.append({
            'action':'meet',
            'location': 'Financial District',
            'person': 'Jeffrey',
           'start_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Financial District'))).strftime('%H:%M'),
            'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'Financial District') + constraints['Jeffrey']['min_meeting_time'])).strftime('%H:%M')
        })
        current_location = 'Financial District'
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'Financial District') + constraints['Jeffrey']['min_meeting_time'])

    # Meet Jason
    jason_start_time = datetime.strptime(constraints['Jason']['start_time'], '%H:%M')
    jason_end_time = datetime.strptime(constraints['Jason']['end_time'], '%H:%M')
    if is_valid_meeting(current_time, jason_start_time, constraints['Jason']['min_meeting_time']):
        schedule.append({
            'action':'meet',
            'location': 'North Beach',
            'person': 'Jason',
           'start_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'North Beach'))).strftime('%H:%M'),
            'end_time': (current_time + timedelta(minutes=calculate_travel_time(current_location, 'North Beach') + constraints['Jason']['min_meeting_time'])).strftime('%H:%M')
        })
        current_location = 'North Beach'
        current_time += timedelta(minutes=calculate_travel_time(current_location, 'North Beach') + constraints['Jason']['min_meeting_time'])

    return schedule

def main():
    schedule = find_optimal_meeting_schedule()
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == "__main__":
    main()