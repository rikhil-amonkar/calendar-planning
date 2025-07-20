import json
import itertools

travel_times = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15
}

friends = [
    {'name': 'Ronald', 'location': 'Nob Hill', 'start_avail': 600, 'end_avail': 1020, 'min_time': 105},
    {'name': 'Helen', 'location': 'The Castro', 'start_avail': 810, 'end_avail': 1020, 'min_time': 120},
    {'name': 'Joshua', 'location': 'Sunset District', 'start_avail': 855, 'end_avail': 1170, 'min_time': 90},
    {'name': 'Margaret', 'location': 'Haight-Ashbury', 'start_avail': 615, 'end_avail': 1320, 'min_time': 60}
]

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    key = (from_loc, to_loc)
    return travel_times[key]

def main():
    n = len(friends)
    for r in range(n, 0, -1):
        for subset in itertools.combinations(friends, r):
            for perm in itertools.permutations(subset):
                current_time = 540
                current_location = 'Pacific Heights'
                candidate = []
                valid = True
                for friend in perm:
                    to_loc = friend['location']
                    tt = get_travel_time(current_location, to_loc)
                    current_time += tt
                    start_meeting = max(current_time, friend['start_avail'])
                    end_meeting = start_meeting + friend['min_time']
                    if end_meeting > friend['end_avail']:
                        valid = False
                        break
                    candidate.append({
                        'action': 'meet',
                        'location': to_loc,
                        'person': friend['name'],
                        'start_time': minutes_to_time(start_meeting),
                        'end_time': minutes_to_time(end_meeting)
                    })
                    current_time = end_meeting
                    current_location = to_loc
                if valid:
                    return {"itinerary": candidate}
    return {"itinerary": []}

if __name__ == '__main__':
    result = main()
    print(json.dumps(result))