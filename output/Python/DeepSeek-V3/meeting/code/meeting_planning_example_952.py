import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    'Bayview': {
        'North Beach': 22,
        'Fisherman\'s Wharf': 25,
        'Haight-Ashbury': 19,
        'Nob Hill': 20,
        'Golden Gate Park': 22,
        'Union Square': 18,
        'Alamo Square': 16,
        'Presidio': 32,
        'Chinatown': 19,
        'Pacific Heights': 23
    },
    'North Beach': {
        'Bayview': 25,
        'Fisherman\'s Wharf': 5,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Golden Gate Park': 22,
        'Union Square': 7,
        'Alamo Square': 16,
        'Presidio': 17,
        'Chinatown': 6,
        'Pacific Heights': 8
    },
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'North Beach': 6,
        'Haight-Ashbury': 22,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Union Square': 13,
        'Alamo Square': 21,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Fisherman\'s Wharf': 23,
        'Nob Hill': 15,
        'Golden Gate Park': 7,
        'Union Square': 19,
        'Alamo Square': 5,
        'Presidio': 15,
        'Chinatown': 19,
        'Pacific Heights': 12
    },
    'Nob Hill': {
        'Bayview': 19,
        'North Beach': 8,
        'Fisherman\'s Wharf': 10,
        'Haight-Ashbury': 13,
        'Golden Gate Park': 17,
        'Union Square': 7,
        'Alamo Square': 11,
        'Presidio': 17,
        'Chinatown': 6,
        'Pacific Heights': 8
    },
    'Golden Gate Park': {
        'Bayview': 23,
        'North Beach': 23,
        'Fisherman\'s Wharf': 24,
        'Haight-Ashbury': 7,
        'Nob Hill': 20,
        'Union Square': 22,
        'Alamo Square': 9,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Fisherman\'s Wharf': 15,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Golden Gate Park': 22,
        'Alamo Square': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'Pacific Heights': 15
    },
    'Alamo Square': {
        'Bayview': 16,
        'North Beach': 15,
        'Fisherman\'s Wharf': 19,
        'Haight-Ashbury': 5,
        'Nob Hill': 11,
        'Golden Gate Park': 9,
        'Union Square': 14,
        'Presidio': 17,
        'Chinatown': 15,
        'Pacific Heights': 10
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Golden Gate Park': 12,
        'Union Square': 22,
        'Alamo Square': 19,
        'Chinatown': 21,
        'Pacific Heights': 11
    },
    'Chinatown': {
        'Bayview': 20,
        'North Beach': 3,
        'Fisherman\'s Wharf': 8,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Golden Gate Park': 23,
        'Union Square': 7,
        'Alamo Square': 17,
        'Presidio': 19,
        'Pacific Heights': 10
    },
    'Pacific Heights': {
        'Bayview': 22,
        'North Beach': 9,
        'Fisherman\'s Wharf': 13,
        'Haight-Ashbury': 11,
        'Nob Hill': 8,
        'Golden Gate Park': 15,
        'Union Square': 12,
        'Alamo Square': 10,
        'Presidio': 11,
        'Chinatown': 11
    }
}

# Friend data
friends = [
    {'name': 'Brian', 'location': 'North Beach', 'start': 13.0, 'end': 19.0, 'duration': 1.5},
    {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start': 11.0, 'end': 12.75, 'duration': 1.0},
    {'name': 'Ashley', 'location': 'Haight-Ashbury', 'start': 15.0, 'end': 20.5, 'duration': 1.5},
    {'name': 'Elizabeth', 'location': 'Nob Hill', 'start': 11.75, 'end': 18.5, 'duration': 1.25},
    {'name': 'Jessica', 'location': 'Golden Gate Park', 'start': 20.0, 'end': 21.75, 'duration': 1.75},
    {'name': 'Deborah', 'location': 'Union Square', 'start': 17.5, 'end': 22.0, 'duration': 1.0},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'start': 17.5, 'end': 21.25, 'duration': 0.75},
    {'name': 'Matthew', 'location': 'Presidio', 'start': 8.25, 'end': 9.0, 'duration': 0.25},
    {'name': 'Kenneth', 'location': 'Chinatown', 'start': 13.75, 'end': 19.5, 'duration': 1.75},
    {'name': 'Anthony', 'location': 'Pacific Heights', 'start': 14.25, 'end': 16.0, 'duration': 0.5}
]

def time_to_float(time_str):
    hours, minutes = map(float, time_str.split(':'))
    return hours + minutes / 60

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule():
    current_location = 'Bayview'
    current_time = 9.0
    itinerary = []
    
    # First meeting with Matthew at Presidio
    travel_time = travel_times[current_location]['Presidio'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[7]['end'] - friends[7]['duration']:
        start_time = max(arrival_time, friends[7]['start'])
        end_time = start_time + friends[7]['duration']
        if end_time <= friends[7]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Presidio',
                'person': 'Matthew',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Presidio'
            current_time = end_time
    
    # Next meeting with Richard at Fisherman's Wharf
    travel_time = travel_times[current_location]['Fisherman\'s Wharf'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[1]['end'] - friends[1]['duration']:
        start_time = max(arrival_time, friends[1]['start'])
        end_time = start_time + friends[1]['duration']
        if end_time <= friends[1]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Fisherman\'s Wharf',
                'person': 'Richard',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Fisherman\'s Wharf'
            current_time = end_time
    
    # Next meeting with Elizabeth at Nob Hill
    travel_time = travel_times[current_location]['Nob Hill'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[3]['end'] - friends[3]['duration']:
        start_time = max(arrival_time, friends[3]['start'])
        end_time = start_time + friends[3]['duration']
        if end_time <= friends[3]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Nob Hill',
                'person': 'Elizabeth',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Nob Hill'
            current_time = end_time
    
    # Next meeting with Anthony at Pacific Heights
    travel_time = travel_times[current_location]['Pacific Heights'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[9]['end'] - friends[9]['duration']:
        start_time = max(arrival_time, friends[9]['start'])
        end_time = start_time + friends[9]['duration']
        if end_time <= friends[9]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Pacific Heights',
                'person': 'Anthony',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Pacific Heights'
            current_time = end_time
    
    # Next meeting with Kenneth at Chinatown
    travel_time = travel_times[current_location]['Chinatown'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[8]['end'] - friends[8]['duration']:
        start_time = max(arrival_time, friends[8]['start'])
        end_time = start_time + friends[8]['duration']
        if end_time <= friends[8]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Chinatown',
                'person': 'Kenneth',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Chinatown'
            current_time = end_time
    
    # Next meeting with Brian at North Beach
    travel_time = travel_times[current_location]['North Beach'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[0]['end'] - friends[0]['duration']:
        start_time = max(arrival_time, friends[0]['start'])
        end_time = start_time + friends[0]['duration']
        if end_time <= friends[0]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'North Beach',
                'person': 'Brian',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'North Beach'
            current_time = end_time
    
    # Next meeting with Ashley at Haight-Ashbury
    travel_time = travel_times[current_location]['Haight-Ashbury'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[2]['end'] - friends[2]['duration']:
        start_time = max(arrival_time, friends[2]['start'])
        end_time = start_time + friends[2]['duration']
        if end_time <= friends[2]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Haight-Ashbury',
                'person': 'Ashley',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Haight-Ashbury'
            current_time = end_time
    
    # Next meeting with Kimberly at Alamo Square
    travel_time = travel_times[current_location]['Alamo Square'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[6]['end'] - friends[6]['duration']:
        start_time = max(arrival_time, friends[6]['start'])
        end_time = start_time + friends[6]['duration']
        if end_time <= friends[6]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Alamo Square',
                'person': 'Kimberly',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Alamo Square'
            current_time = end_time
    
    # Next meeting with Deborah at Union Square
    travel_time = travel_times[current_location]['Union Square'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[5]['end'] - friends[5]['duration']:
        start_time = max(arrival_time, friends[5]['start'])
        end_time = start_time + friends[5]['duration']
        if end_time <= friends[5]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Union Square',
                'person': 'Deborah',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = 'Union Square'
            current_time = end_time
    
    # Final meeting with Jessica at Golden Gate Park
    travel_time = travel_times[current_location]['Golden Gate Park'] / 60
    arrival_time = current_time + travel_time
    if arrival_time <= friends[4]['end'] - friends[4]['duration']:
        start_time = max(arrival_time, friends[4]['start'])
        end_time = start_time + friends[4]['duration']
        if end_time <= friends[4]['end']:
            itinerary.append({
                'action': 'meet',
                'location': 'Golden Gate Park',
                'person': 'Jessica',
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
    
    return itinerary

def main():
    itinerary = calculate_schedule()
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()