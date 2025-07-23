import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    'The Castro': {
        'Marina District': 21,
        'Presidio': 20,
        'North Beach': 20,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Golden Gate Park': 11,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Sunset District': 17
    },
    'Marina District': {
        'The Castro': 22,
        'Presidio': 10,
        'North Beach': 11,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Sunset District': 19
    },
    'Presidio': {
        'The Castro': 21,
        'Marina District': 11,
        'North Beach': 18,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Sunset District': 15
    },
    'North Beach': {
        'The Castro': 23,
        'Marina District': 9,
        'Presidio': 17,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Alamo Square': 16,
        'Financial District': 8,
        'Sunset District': 27
    },
    'Embarcadero': {
        'The Castro': 25,
        'Marina District': 12,
        'Presidio': 20,
        'North Beach': 5,
        'Haight-Ashbury': 21,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Alamo Square': 19,
        'Financial District': 5,
        'Sunset District': 30
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Marina District': 17,
        'Presidio': 15,
        'North Beach': 19,
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Richmond District': 10,
        'Alamo Square': 5,
        'Financial District': 21,
        'Sunset District': 15
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Marina District': 16,
        'Presidio': 11,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Alamo Square': 9,
        'Financial District': 26,
        'Sunset District': 10
    },
    'Richmond District': {
        'The Castro': 16,
        'Marina District': 9,
        'Presidio': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Golden Gate Park': 9,
        'Alamo Square': 13,
        'Financial District': 22,
        'Sunset District': 11
    },
    'Alamo Square': {
        'The Castro': 8,
        'Marina District': 15,
        'Presidio': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Financial District': 17,
        'Sunset District': 16
    },
    'Financial District': {
        'The Castro': 20,
        'Marina District': 15,
        'Presidio': 22,
        'North Beach': 7,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Sunset District': 30
    },
    'Sunset District': {
        'The Castro': 17,
        'Marina District': 21,
        'Presidio': 16,
        'North Beach': 28,
        'Embarcadero': 30,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 11,
        'Richmond District': 12,
        'Alamo Square': 17,
        'Financial District': 30
    }
}

# Meeting constraints
meetings = [
    {'person': 'Elizabeth', 'location': 'Marina District', 'start': 19.0, 'end': 20.75, 'duration': 1.75},
    {'person': 'Joshua', 'location': 'Presidio', 'start': 8.5, 'end': 13.25, 'duration': 1.75},
    {'person': 'Timothy', 'location': 'North Beach', 'start': 19.75, 'end': 22.0, 'duration': 1.5},
    {'person': 'David', 'location': 'Embarcadero', 'start': 10.75, 'end': 12.5, 'duration': 0.5},
    {'person': 'Kimberly', 'location': 'Haight-Ashbury', 'start': 16.75, 'end': 21.5, 'duration': 1.25},
    {'person': 'Lisa', 'location': 'Golden Gate Park', 'start': 17.5, 'end': 21.75, 'duration': 0.75},
    {'person': 'Ronald', 'location': 'Richmond District', 'start': 8.0, 'end': 9.5, 'duration': 1.5},
    {'person': 'Stephanie', 'location': 'Alamo Square', 'start': 15.5, 'end': 16.5, 'duration': 0.5},
    {'person': 'Helen', 'location': 'Financial District', 'start': 17.5, 'end': 18.5, 'duration': 0.75},
    {'person': 'Laura', 'location': 'Sunset District', 'start': 17.75, 'end': 21.25, 'duration': 1.5}
]

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule():
    current_location = 'The Castro'
    current_time = 9.0  # 9:00 AM
    itinerary = []
    
    # Ronald is earliest available
    ronald = next(m for m in meetings if m['person'] == 'Ronald')
    travel_time = travel_times[current_location][ronald['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= ronald['start']:
        start_time = ronald['start']
    else:
        start_time = arrival_time
    end_time = start_time + ronald['duration']
    if end_time > ronald['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': ronald['location'],
        'person': ronald['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = ronald['location']
    current_time = end_time
    
    # Next is Joshua
    joshua = next(m for m in meetings if m['person'] == 'Joshua')
    travel_time = travel_times[current_location][joshua['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= joshua['start']:
        start_time = joshua['start']
    else:
        start_time = arrival_time
    end_time = start_time + joshua['duration']
    if end_time > joshua['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': joshua['location'],
        'person': joshua['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = joshua['location']
    current_time = end_time
    
    # Next is David
    david = next(m for m in meetings if m['person'] == 'David')
    travel_time = travel_times[current_location][david['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= david['start']:
        start_time = david['start']
    else:
        start_time = arrival_time
    end_time = start_time + david['duration']
    if end_time > david['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': david['location'],
        'person': david['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = david['location']
    current_time = end_time
    
    # Next is Stephanie
    stephanie = next(m for m in meetings if m['person'] == 'Stephanie')
    travel_time = travel_times[current_location][stephanie['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= stephanie['start']:
        start_time = stephanie['start']
    else:
        start_time = arrival_time
    end_time = start_time + stephanie['duration']
    if end_time > stephanie['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': stephanie['location'],
        'person': stephanie['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = stephanie['location']
    current_time = end_time
    
    # Next is Helen
    helen = next(m for m in meetings if m['person'] == 'Helen')
    travel_time = travel_times[current_location][helen['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= helen['start']:
        start_time = helen['start']
    else:
        start_time = arrival_time
    end_time = start_time + helen['duration']
    if end_time > helen['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': helen['location'],
        'person': helen['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = helen['location']
    current_time = end_time
    
    # Next is Kimberly
    kimberly = next(m for m in meetings if m['person'] == 'Kimberly')
    travel_time = travel_times[current_location][kimberly['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= kimberly['start']:
        start_time = kimberly['start']
    else:
        start_time = arrival_time
    end_time = start_time + kimberly['duration']
    if end_time > kimberly['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': kimberly['location'],
        'person': kimberly['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = kimberly['location']
    current_time = end_time
    
    # Next is Lisa
    lisa = next(m for m in meetings if m['person'] == 'Lisa')
    travel_time = travel_times[current_location][lisa['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= lisa['start']:
        start_time = lisa['start']
    else:
        start_time = arrival_time
    end_time = start_time + lisa['duration']
    if end_time > lisa['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': lisa['location'],
        'person': lisa['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = lisa['location']
    current_time = end_time
    
    # Next is Laura
    laura = next(m for m in meetings if m['person'] == 'Laura')
    travel_time = travel_times[current_location][laura['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= laura['start']:
        start_time = laura['start']
    else:
        start_time = arrival_time
    end_time = start_time + laura['duration']
    if end_time > laura['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': laura['location'],
        'person': laura['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = laura['location']
    current_time = end_time
    
    # Next is Elizabeth
    elizabeth = next(m for m in meetings if m['person'] == 'Elizabeth')
    travel_time = travel_times[current_location][elizabeth['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= elizabeth['start']:
        start_time = elizabeth['start']
    else:
        start_time = arrival_time
    end_time = start_time + elizabeth['duration']
    if end_time > elizabeth['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': elizabeth['location'],
        'person': elizabeth['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    current_location = elizabeth['location']
    current_time = end_time
    
    # Finally Timothy
    timothy = next(m for m in meetings if m['person'] == 'Timothy')
    travel_time = travel_times[current_location][timothy['location']] / 60.0
    arrival_time = current_time + travel_time
    if arrival_time <= timothy['start']:
        start_time = timothy['start']
    else:
        start_time = arrival_time
    end_time = start_time + timothy['duration']
    if end_time > timothy['end']:
        return None
    itinerary.append({
        'action': 'meet',
        'location': timothy['location'],
        'person': timothy['person'],
        'start_time': float_to_time(start_time),
        'end_time': float_to_time(end_time)
    })
    
    return itinerary

def main():
    itinerary = calculate_schedule()
    if itinerary:
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print(json.dumps({'itinerary': []}, indent=2))

if __name__ == '__main__':
    main()