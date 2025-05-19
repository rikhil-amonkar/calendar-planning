import json

def parse_time(time_str):
    time_str = time_str.upper().replace(' ', '')
    if ':' in time_str:
        time_part, period = time_str[:-2], time_str[-2:]
        hours, minutes = map(int, time_part.split(':'))
    else:
        hours = int(time_str[:-2])
        minutes = 0
        period = time_str[-2:]
    if period == 'PM' and hours != 12:
        hours += 12
    elif period == 'AM' and hours == 12:
        hours = 0
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    min = m % 60
    return f"{h}:{min:02d}"

travel_times = {}
travel_data = [
    "Richmond District to The Castro: 16",
    "Richmond District to Nob Hill: 17",
    "Richmond District to Marina District: 9",
    "Richmond District to Pacific Heights: 10",
    "Richmond District to Haight-Ashbury: 10",
    "Richmond District to Mission District: 20",
    "Richmond District to Chinatown: 20",
    "Richmond District to Russian Hill: 13",
    "Richmond District to Alamo Square: 13",
    "Richmond District to Bayview: 27",
    "The Castro to Richmond District: 16",
    "The Castro to Nob Hill: 16",
    "The Castro to Marina District: 21",
    "The Castro to Pacific Heights: 16",
    "The Castro to Haight-Ashbury: 6",
    "The Castro to Mission District: 7",
    "The Castro to Chinatown: 22",
    "The Castro to Russian Hill: 18",
    "The Castro to Alamo Square: 8",
    "The Castro to Bayview: 19",
    "Nob Hill to Richmond District: 14",
    "Nob Hill to The Castro: 17",
    "Nob Hill to Marina District: 11",
    "Nob Hill to Pacific Heights: 8",
    "Nob Hill to Haight-Ashbury: 13",
    "Nob Hill to Mission District: 13",
    "Nob Hill to Chinatown: 6",
    "Nob Hill to Russian Hill: 5",
    "Nob Hill to Alamo Square: 11",
    "Nob Hill to Bayview: 19",
    "Marina District to Richmond District: 11",
    "Marina District to The Castro: 22",
    "Marina District to Nob Hill: 12",
    "Marina District to Pacific Heights: 7",
    "Marina District to Haight-Ashbury: 16",
    "Marina District to Mission District: 20",
    "Marina District to Chinatown: 15",
    "Marina District to Russian Hill: 8",
    "Marina District to Alamo Square: 15",
    "Marina District to Bayview: 27",
    "Pacific Heights to Richmond District: 12",
    "Pacific Heights to The Castro: 16",
    "Pacific Heights to Nob Hill: 8",
    "Pacific Heights to Marina District: 6",
    "Pacific Heights to Haight-Ashbury: 11",
    "Pacific Heights to Mission District: 15",
    "Pacific Heights to Chinatown: 11",
    "Pacific Heights to Russian Hill: 7",
    "Pacific Heights to Alamo Square: 10",
    "Pacific Heights to Bayview: 22",
    "Haight-Ashbury to Richmond District: 10",
    "Haight-Ashbury to The Castro: 6",
    "Haight-Ashbury to Nob Hill: 15",
    "Haight-Ashbury to Marina District: 17",
    "Haight-Ashbury to Pacific Heights: 12",
    "Haight-Ashbury to Mission District: 11",
    "Haight-Ashbury to Chinatown: 19",
    "Haight-Ashbury to Russian Hill: 17",
    "Haight-Ashbury to Alamo Square: 5",
    "Haight-Ashbury to Bayview: 18",
    "Mission District to Richmond District: 20",
    "Mission District to The Castro: 7",
    "Mission District to Nob Hill: 12",
    "Mission District to Marina District: 19",
    "Mission District to Pacific Heights: 16",
    "Mission District to Haight-Ashbury: 12",
    "Mission District to Chinatown: 16",
    "Mission District to Russian Hill: 15",
    "Mission District to Alamo Square: 11",
    "Mission District to Bayview: 14",
    "Chinatown to Richmond District: 20",
    "Chinatown to The Castro: 22",
    "Chinatown to Nob Hill: 9",
    "Chinatown to Marina District: 12",
    "Chinatown to Pacific Heights: 10",
    "Chinatown to Haight-Ashbury: 19",
    "Chinatown to Mission District: 17",
    "Chinatown to Russian Hill: 7",
    "Chinatown to Alamo Square: 17",
    "Chinatown to Bayview: 20",
    "Russian Hill to Richmond District: 14",
    "Russian Hill to The Castro: 21",
    "Russian Hill to Nob Hill: 5",
    "Russian Hill to Marina District: 7",
    "Russian Hill to Pacific Heights: 7",
    "Russian Hill to Haight-Ashbury: 17",
    "Russian Hill to Mission District: 16",
    "Russian Hill to Chinatown: 9",
    "Russian Hill to Alamo Square: 15",
    "Russian Hill to Bayview: 23",
    "Alamo Square to Richmond District: 11",
    "Alamo Square to The Castro: 8",
    "Alamo Square to Nob Hill: 11",
    "Alamo Square to Marina District: 15",
    "Alamo Square to Pacific Heights: 10",
    "Alamo Square to Haight-Ashbury: 5",
    "Alamo Square to Mission District: 10",
    "Alamo Square to Chinatown: 15",
    "Alamo Square to Russian Hill: 13",
    "Alamo Square to Bayview: 16",
    "Bayview to Richmond District: 25",
    "Bayview to The Castro: 19",
    "Bayview to Nob Hill: 20",
    "Bayview to Marina District: 27",
    "Bayview to Pacific Heights: 23",
    "Bayview to Haight-Ashbury: 19",
    "Bayview to Mission District: 13",
    "Bayview to Chinatown: 19",
    "Bayview to Russian Hill: 23",
    "Bayview to Alamo Square: 16",
]

for line in travel_data:
    start_loc, rest = line.split(' to ', 1)
    end_loc, time_part = rest.split(': ', 1)
    time = int(time_part)
    if start_loc not in travel_times:
        travel_times[start_loc] = {}
    travel_times[start_loc][end_loc] = time

friends = [
    {'name': 'Matthew', 'location': 'The Castro', 'start': parse_time('4:30PM'), 'end': parse_time('8:00PM'), 'duration':45},
    {'name': 'Rebecca', 'location': 'Nob Hill', 'start': parse_time('3:15PM'), 'end': parse_time('7:15PM'), 'duration':105},
    {'name': 'Brian', 'location': 'Marina District', 'start': parse_time('2:15PM'), 'end': parse_time('10:00PM'), 'duration':30},
    {'name': 'Emily', 'location': 'Pacific Heights', 'start': parse_time('11:15AM'), 'end': parse_time('7:45PM'), 'duration':15},
    {'name': 'Karen', 'location': 'Haight-Ashbury', 'start': parse_time('11:45AM'), 'end': parse_time('5:30PM'), 'duration':30},
    {'name': 'Stephanie', 'location': 'Mission District', 'start': parse_time('1:00PM'), 'end': parse_time('3:45PM'), 'duration':75},
    {'name': 'James', 'location': 'Chinatown', 'start': parse_time('2:30PM'), 'end': parse_time('7:00PM'), 'duration':120},
    {'name': 'Steven', 'location': 'Russian Hill', 'start': parse_time('2:00PM'), 'end': parse_time('8:00PM'), 'duration':30},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': parse_time('1:00PM'), 'end': parse_time('5:15PM'), 'duration':120},
    {'name': 'William', 'location': 'Bayview', 'start': parse_time('6:15PM'), 'end': parse_time('8:15PM'), 'duration':90},
]

friends.sort(key=lambda x: (-x['duration'], x['end']))

current_time = parse_time('9:00AM')
current_location = 'Richmond District'
itinerary = []

for friend in friends:
    if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
        continue
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    earliest_start = max(arrival_time, friend['start'])
    latest_start = friend['end'] - friend['duration']
    
    if earliest_start > latest_start:
        continue
    
    start = earliest_start
    end = start + friend['duration']
    
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start),
        'end_time': minutes_to_time(end)
    })
    
    current_time = end
    current_location = friend['location']

print(json.dumps({'itinerary': itinerary}, indent=2))