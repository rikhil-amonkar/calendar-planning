import heapq
import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'David',
        'location': 'Sunset District',
        'S': 9 * 60 + 15,  # 555
        'L': (22 * 60) - 15,  # 1305
        'D': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'S': 21 * 60 + 15,  # 1275
        'L': (21 * 60 + 45) - 15,  # 1275
        'D': 15
    },
    {
        'name': 'Patricia',
        'location': 'Nob Hill',
        'S': 15 * 60,  # 900
        'L': (19 * 60 + 15) - 120,  # 1035
        'D': 120
    },
    {
        'name': 'Mary',
        'location': 'Marina District',
        'S': 14 * 60 + 45,  # 885
        'L': (16 * 60 + 45) - 45,  # 960
        'D': 45
    },
    {
        'name': 'Charles',
        'location': 'Richmond District',
        'S': 17 * 60 + 15,  # 1035
        'L': (21 * 60) - 15,  # 1245
        'D': 15
    },
    {
        'name': 'Joshua',
        'location': 'Financial District',
        'S': 14 * 60 + 30,  # 870
        'L': (17 * 60 + 15) - 90,  # 945
        'D': 90
    },
    {
        'name': 'Ronald',
        'location': 'Embarcadero',
        'S': 18 * 60 + 15,  # 1095
        'L': (20 * 60 + 45) - 30,  # 1215
        'D': 30
    },
    {
        'name': 'George',
        'location': 'The Castro',
        'S': 14 * 60 + 15,  # 855
        'L': (19 * 60) - 105,  # 1035
        'D': 105
    },
    {
        'name': 'Kimberly',
        'location': 'Alamo Square',
        'S': 9 * 60,  # 540
        'L': (14 * 60 + 30) - 105,  # 765
        'D': 105
    },
    {
        'name': 'William',
        'location': 'Presidio',
        'S': 7 * 60,  # 420
        'L': (12 * 60 + 45) - 60,  # 705
        'D': 60
    },
]

travel_time = {
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Presidio'): 20,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Presidio'): 17,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Alamo Square'): 19,
}

heap = []
heapq.heappush(heap, (0, 540, 'Russian Hill', 0, []))  # priority is -num_visited, num_visited is 0
best = {}
max_visited = 0
best_itinerary = []

while heap:
    priority, current_time, current_loc, bitmask, itinerary = heapq.heappop(heap)
    num_visited = -priority

    key = (current_loc, bitmask)
    if key in best:
        if current_time >= best[key]:
            continue
    best[key] = current_time

    if num_visited > max_visited:
        max_visited = num_visited
        best_itinerary = itinerary
    elif num_visited == max_visited and len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary

    for idx in range(len(friends)):
        if not (bitmask & (1 << idx)):
            friend = friends[idx]
            loc = friend['location']
            if (current_loc, loc) not in travel_time:
                continue
            travel_minutes = travel_time[(current_loc, loc)]
            arrival_time = current_time + travel_minutes
            if arrival_time > friend['L']:
                continue
            start_time_meeting = max(arrival_time, friend['S'])
            end_time_meeting = start_time_meeting + friend['D']
            new_itinerary = itinerary + [{
                'action': 'meet',
                'location': loc,
                'person': friend['name'],
                'start_time': time_to_str(start_time_meeting),
                'end_time': time_to_str(end_time_meeting)
            }]
            new_bitmask = bitmask | (1 << idx)
            heapq.heappush(heap, (-(num_visited + 1), end_time_meeting, loc, new_bitmask, new_itinerary))

# Output the best itinerary
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))