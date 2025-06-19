import json
from datetime import datetime, timedelta

# Define travel distances (in minutes)
travel_distances = {
    'Presidio': {
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Fisherman\'s Wharf': 19,
        'Marina District': 11,
        'Alamo Square': 19,
        'Sunset District': 15,
        'Nob Hill': 18,
        'North Beach': 18
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Golden Gate Park': 15,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Alamo Square': 10,
        'Sunset District': 21,
        'Nob Hill': 8,
        'North Beach': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Pacific Heights': 16,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Alamo Square': 9,
        'Sunset District': 10,
        'Nob Hill': 20,
        'North Beach': 23
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Pacific Heights': 12,
        'Golden Gate Park': 25,
        'Marina District': 9,
        'Alamo Square': 21,
        'Sunset District': 27,
        'Nob Hill': 11,
        'North Beach': 6
    },
    'Marina District': {
        'Presidio': 10,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Fisherman\'s Wharf': 10,
        'Alamo Square': 15,
        'Sunset District': 19,
        'Nob Hill': 12,
        'North Beach': 11
    },
    'Alamo Square': {
        'Presidio': 17,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
        'Sunset District': 16,
        'Nob Hill': 11,
        'North Beach': 15
    },
    'Sunset District': {
        'Presidio': 16,
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'Fisherman\'s Wharf': 29,
        'Marina District': 21,
        'Alamo Square': 17,
        'Nob Hill': 27,
        'North Beach': 28
    },
    'Nob Hill': {
        'Presidio': 17,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Fisherman\'s Wharf': 10,
        'Marina District': 11,
        'Alamo Square': 11,
        'Sunset District': 24,
        'North Beach': 8
    },
    'North Beach': {
        'Presidio': 17,
        'Pacific Heights': 8,
        'Golden Gate Park': 22,
        'Fisherman\'s Wharf': 5,
        'Marina District': 9,
        'Alamo Square': 16,
        'Sunset District': 27,
        'Nob Hill': 7
    }
}

# Define meeting constraints
meeting_constraints = {
    'Kevin': {'start_time': '07:15', 'end_time': '08:45', 'duration': 90},
    'Michelle': {'start_time': '20:00', 'end_time': '21:00', 'duration': 15},
    'Emily': {'start_time': '16:15', 'end_time': '19:00', 'duration': 30},
    'Mark': {'start_time': '18:15', 'end_time': '20:45', 'duration': 75},
    'Barbara': {'start_time': '17:00', 'end_time': '19:00', 'duration': 120},
    'Laura': {'start_time': '19:00', 'end_time': '21:15', 'duration': 75},
    'Mary': {'start_time': '17:30', 'end_time': '19:00', 'duration': 45},
    'Helen': {'start_time': '11:00', 'end_time': '12:15', 'duration': 45}
}

def calculate_travel_time(location1, location2):
    return travel_distances[location1][location2]

def is_meeting_possible(person, start_time, end_time):
    person_start_time = datetime.strptime(meeting_constraints[person]['start_time'], '%H:%M')
    person_end_time = datetime.strptime(meeting_constraints[person]['end_time'], '%H:%M')
    return (person_start_time <= start_time and start_time <= person_end_time) or (person_start_time <= end_time and end_time <= person_end_time)

def get_optimal_schedule():
    schedule = []
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')  # Assuming meetings end by 5 PM

    # Meet Kevin
    schedule.append({'action':'meet', 'location': 'Pacific Heights', 'person': 'Kevin','start_time': '09:00', 'end_time': '10:30'})
    start_time = datetime.strptime('10:30', '%H:%M')
    end_time = datetime.strptime('10:30', '%H:%M') + timedelta(minutes=calculate_travel_time('Pacific Heights', 'Presidio'))

    # Meet Helen
    schedule.append({'action':'meet', 'location': 'North Beach', 'person': 'Helen','start_time': '11:00', 'end_time': '12:15'})
    start_time = datetime.strptime('12:15', '%H:%M')
    end_time = datetime.strptime('12:15', '%H:%M') + timedelta(minutes=calculate_travel_time('North Beach', 'Presidio'))

    # Meet Michelle
    schedule.append({'action':'meet', 'location': 'Golden Gate Park', 'person': 'Michelle','start_time': '20:00', 'end_time': '20:15'})
    start_time = datetime.strptime('20:15', '%H:%M')
    end_time = datetime.strptime('20:15', '%H:%M') + timedelta(minutes=calculate_travel_time('Golden Gate Park', 'Presidio'))

    # Meet Emily
    schedule.append({'action':'meet', 'location': 'Fisherman\'s Wharf', 'person': 'Emily','start_time': '16:15', 'end_time': '19:00'})
    start_time = datetime.strptime('19:00', '%H:%M')
    end_time = datetime.strptime('19:00', '%H:%M') + timedelta(minutes=calculate_travel_time('Fisherman\'s Wharf', 'Presidio'))

    # Meet Mark
    schedule.append({'action':'meet', 'location': 'Marina District', 'person': 'Mark','start_time': '18:15', 'end_time': '20:45'})
    start_time = datetime.strptime('20:45', '%H:%M')
    end_time = datetime.strptime('20:45', '%H:%M') + timedelta(minutes=calculate_travel_time('Marina District', 'Presidio'))

    # Meet Barbara
    schedule.append({'action':'meet', 'location': 'Alamo Square', 'person': 'Barbara','start_time': '17:00', 'end_time': '19:00'})
    start_time = datetime.strptime('19:00', '%H:%M')
    end_time = datetime.strptime('19:00', '%H:%M') + timedelta(minutes=calculate_travel_time('Alamo Square', 'Presidio'))

    # Meet Laura
    schedule.append({'action':'meet', 'location': 'Sunset District', 'person': 'Laura','start_time': '19:00', 'end_time': '21:15'})
    start_time = datetime.strptime('21:15', '%H:%M')
    end_time = datetime.strptime('21:15', '%H:%M') + timedelta(minutes=calculate_travel_time('Sunset District', 'Presidio'))

    # Meet Mary
    schedule.append({'action':'meet', 'location': 'Nob Hill', 'person': 'Mary','start_time': '17:30', 'end_time': '19:00'})
    start_time = datetime.strptime('19:00', '%H:%M')
    end_time = datetime.strptime('19:00', '%H:%M') + timedelta(minutes=calculate_travel_time('Nob Hill', 'Presidio'))

    return schedule

def main():
    schedule = get_optimal_schedule()
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == "__main__":
    main()