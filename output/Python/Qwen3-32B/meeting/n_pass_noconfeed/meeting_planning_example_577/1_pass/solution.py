import json
from itertools import permutations

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Robert',
        'location': 'Nob Hill',
        'available_start': 7 * 60 + 45,  # 7:45 AM
        'available_end': 10 * 60 + 30,   # 10:30 AM
        'required_duration': 90
    },
    {
        'name': 'Steven',
        'location': 'Golden Gate Park',
        'available_start': 8 * 60 + 30,  # 8:30 AM
        'available_end': 17 * 60,        # 5:00 PM
        'required_duration': 75
    },
    {
        'name': 'Anthony',
        'location': 'Alamo Square',
        'available_start': 7 * 60 + 45,  # 7:45 AM
        'available_end': 19 * 60 + 45,   # 7:45 PM
        'required_duration': 15
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'available_start': 14 * 60 + 45, # 2:45 PM
        'available_end': 21 * 60 + 45,   # 9:45 PM
        'required_duration': 45
    },
    {
        'name': 'Kevin',
        'location': "Fisherman's Wharf",
        'available_start': 19 * 60 + 15, # 7:15 PM
        'available_end': 21 * 60 + 45,   # 9:45 PM
        'required_duration': 75
    },
    {
        'name': 'Stephanie',
        'location': 'Russian Hill',
        'available_start': 20 * 60,      # 8:00 PM
        'available_end': 20 * 60 + 45,   # 8:45 PM
        'required_duration': 15
    }
]

travel_times = {
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Pacific Heights'): 7,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Russian Hill'): 7,
    ("Fisherman's Wharf", 'Nob Hill'): 11,
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Alamo Square'): 20,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', "Fisherman's Wharf"): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', "Fisherman's Wharf"): 19,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
}

best_itinerary = []
max_friends = 0
best_end_time = float('inf')

for k in range(1, 7):
    for perm in permutations(friends, k):
        current_time = 540  # 9:00 AM
        current_location = 'Haight-Ashbury'
        itinerary = []
        valid = True
        for friend in perm:
            from_loc = current_location
            to_loc = friend['location']
            if (from_loc, to_loc) not in travel_times:
                valid = False
                break
            travel_time = travel_times[(from_loc, to_loc)]
            arrival_time = current_time + travel_time
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required_duration']
            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - required
            if earliest_start > latest_start:
                valid = False
                break
            # Add to itinerary
            itinerary.append( (friend['name'], friend['location"], earliest_start, earliest_start + required) )
            current_time = earliest_start + required
            current_location = to_loc
        if valid:
            if len(itinerary) > max_friends:
                max_friends = len(itinerary)
                best_itinerary = itinerary
                best_end_time = current_time
            elif len(itinerary) == max_friends:
                if current_time < best_end_time:
                    best_itinerary = itinerary
                    best_end_time = current_time

# Convert best_itinerary to JSON format
json_itinerary = []
for name, location, start, end in best_itinerary:
    json_itinerary.append({
        "action": "meet",
        "location": location,
        "person": name,
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })

result = {"itinerary": json_itinerary}
print(json.dumps(result, indent=2))