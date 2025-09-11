import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Emily',
        'location': 'Russian Hill',
        'available_start': 735,
        'available_end': 855,
        'required_duration': 105
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'available_start': 885,
        'available_end': 1170,
        'required_duration': 60
    },
    {
        'name': 'Deborah',
        'location': 'Chinatown',
        'available_start': 450,
        'available_end': 930,
        'required_duration': 45
    },
    {
        'name': 'Margaret',
        'location': 'Sunset District',
        'available_start': 21 * 60 + 30,  # 1290
        'available_end': 22 * 60 + 30,    # 1350
        'required_duration': 60
    },
    {
        'name': 'George',
        'location': 'The Castro',
        'available_start': 450,
        'available_end': 855,
        'required_duration': 60
    },
    {
        'name': 'Andrew',
        'location': 'Embarcadero',
        'available_start': 20 * 60 + 15,  # 1215
        'available_end': 22 * 60 + 0,     # 1320
        'required_duration': 75
    },
    {
        'name': 'Steven',
        'location': 'Golden Gate Park',
        'available_start': 675,
        'available_end': 21 * 60 + 15,    # 1275
        'required_duration': 105
    }
]

loc_index = {
    'Alamo Square': 0,
    'Russian Hill': 1,
    'Presidio': 2,
    'Chinatown': 3,
    'Sunset District': 4,
    'The Castro': 5,
    'Embarcadero': 6,
    'Golden Gate Park': 7
}

for friend in friends:
    friend['loc_idx'] = loc_index[friend['location']]

travel_time = [
    [0, 13, 18, 16, 16, 8, 17, 9],
    [15, 0, 14, 9, 23, 21, 8, 21],
    [18, 14, 0, 21, 15, 21, 20, 12],
    [17, 7, 19, 0, 29, 22, 5, 23],
    [17, 24, 16, 30, 0, 17, 31, 11],
    [8, 18, 20, 20, 17, 0, 22, 11],
    [19, 8, 20, 7, 30, 25, 0, 25],
    [10, 19, 11, 23, 10, 13, 25, 0]
]

best_itinerary = []

def dfs(current_time, current_loc, visited, itinerary):
    global best_itinerary
    if len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary.copy()
    for i in range(len(friends)):
        if not (visited & (1 << i)):
            friend = friends[i]
            arrival_time = current_time + travel_time[current_loc][friend['loc_idx']]
            if arrival_time > (friend['available_end'] - friend['required_duration']):
                continue
            start_time = max(friend['available_start'], arrival_time)
            end_time = start_time + friend['required_duration']
            new_visited = visited | (1 << i)
            new_itinerary = itinerary + [(friend, start_time, end_time)]
            dfs(end_time, friend['loc_idx'], new_visited, new_itinerary)

dfs(540, 0, 0, [])

itinerary_json = {
    "itinerary": [
        {
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time_str(start),
            "end_time": minutes_to_time_str(end)
        }
        for (friend, start, end) in best_itinerary
    ]
}

print(json.dumps(itinerary_json, indent=2))