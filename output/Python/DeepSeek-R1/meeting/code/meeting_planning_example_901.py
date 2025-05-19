import json

def parse_time(time_str):
    time_str = time_str.upper().replace(':', '').replace('AM', '').replace('PM', '')
    if 'AM' in time_str.upper() or 'PM' in time_str.upper():
        period = time_str[-2:]
        time_str = time_str[:-2]
    else:
        period = ''
    if len(time_str) == 3:
        hour = int(time_str[0])
        minutes = int(time_str[1:3])
    else:
        hour = int(time_str[:2]) if len(time_str) >= 2 else 0
        minutes = int(time_str[2:4]) if len(time_str) >=4 else 0
    if period == 'PM' and hour != 12:
        hour += 12
    if period == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minutes

travel_times = {
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Richmond District'): 14,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Richmond District'): 12,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Richmond District'): 18,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Richmond District'): 20,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Richmond District'): 11,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Richmond District'): 25,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Bayview'): 27
}

friends = [
    {
        'name': 'Emily',
        'location': 'Pacific Heights',
        'available_start': parse_time('9:15AM'),
        'available_end': parse_time('1:45PM'),
        'duration': 120
    },
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': parse_time('1:45PM'),
        'available_end': parse_time('6:45PM'),
        'duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Golden Gate Park',
        'available_start': parse_time('6:45PM'),
        'available_end': parse_time('9:15PM'),
        'duration': 75
    },
    {
        'name': 'James',
        'location': 'Embarcadero',
        'available_start': parse_time('10:30AM'),
        'available_end': parse_time('11:30AM'),
        'duration': 30
    },
    {
        'name': 'Linda',
        'location': 'Haight-Ashbury',
        'available_start': parse_time('7:30AM'),
        'available_end': parse_time('7:15PM'),
        'duration': 15
    },
    {
        'name': 'Paul',
        'location': 'Fisherman\'s Wharf',
        'available_start': parse_time('2:45PM'),
        'available_end': parse_time('6:45PM'),
        'duration': 90
    },
    {
        'name': 'Anthony',
        'location': 'Mission District',
        'available_start': parse_time('8:00AM'),
        'available_end': parse_time('2:45PM'),
        'duration': 105
    },
    {
        'name': 'Nancy',
        'location': 'Alamo Square',
        'available_start': parse_time('8:30AM'),
        'available_end': parse_time('1:45PM'),
        'duration': 120
    },
    {
        'name': 'William',
        'location': 'Bayview',
        'available_start': parse_time('5:30PM'),
        'available_end': parse_time('8:30PM'),
        'duration': 120
    },
    {
        'name': 'Margaret',
        'location': 'Richmond District',
        'available_start': parse_time('3:15PM'),
        'available_end': parse_time('6:15PM'),
        'duration': 45
    }
]

current_time = parse_time('9:00AM')
current_location = 'Russian Hill'
itinerary = []

schedule_order = ['Nancy', 'Emily', 'Helen', 'Linda', 'Margaret', 'Paul', 'William']

for name in schedule_order:
    friend = next(f for f in friends if f['name'] == name)
    travel_time = travel_times.get((current_location, friend['location']), 0)
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, friend['available_start'])
    if start_time + friend['duration'] > friend['available_end']:
        continue
    itinerary.append({
        'location': friend['location'],
        'person': friend['name'],
        'start': start_time,
        'end': start_time + friend['duration']
    })
    current_time = start_time + friend['duration']
    current_location = friend['location']

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    time_str = f"{hours}:{mins:02d}"
    return time_str.lstrip('0') if time_str.startswith('0') else time_str

formatted = []
for item in itinerary:
    formatted.append({
        'action': 'meet',
        'location': item['location'],
        'person': item['person'],
        'start_time': format_time(item['start']).replace(':0', ':') if mins ==0 else format_time(item['start']),
        'end_time': format_time(item['end']).replace(':0', ':') if mins ==0 else format_time(item['end'])
    })

print(json.dumps({'itinerary': formatted}, indent=2))