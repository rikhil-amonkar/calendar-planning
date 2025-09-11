import heapq
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'index': 0,
            'name': 'Mark',
            'location': "Fisherman's Wharf",
            'start': 8 * 60 + 15,  # 495
            'end': 10 * 60,        # 600
            'duration': 30
        },
        {
            'index': 1,
            'name': 'Stephanie',
            'location': 'Presidio',
            'start': 12 * 60 + 15, # 735
            'end': 15 * 60,        # 900
            'duration': 75
        },
        {
            'index': 2,
            'name': 'Betty',
            'location': 'Bayview',
            'start': 7 * 60 + 15,  # 435
            'end': 20 * 60 + 30,   # 1230
            'duration': 15
        },
        {
            'index': 3,
            'name': 'Lisa',
            'location': 'Haight-Ashbury',
            'start': 15 * 60 + 30, # 930
            'end': 18 * 60 + 30,   # 1110
            'duration': 45
        },
        {
            'index': 4,
            'name': 'William',
            'location': 'Russian Hill',
            'start': 18 * 60 + 45, # 1125
            'end': 20 * 60,        # 1200
            'duration': 60
        },
        {
            'index': 5,
            'name': 'Brian',
            'location': 'The Castro',
            'start': 9 * 60 + 15,  # 555
            'end': 13 * 60 + 15,   # 795
            'duration': 30
        },
        {
            'index': 6,
            'name': 'Joseph',
            'location': 'Marina District',
            'start': 10 * 60 + 45, # 645
            'end': 15 * 60,        # 900
            'duration': 90
        },
        {
            'index': 7,
            'name': 'Ashley',
            'location': 'Richmond District',
            'start': 9 * 60 + 45,  # 585
            'end': 11 * 60 + 15,   # 675
            'duration': 45
        },
        {
            'index': 8,
            'name': 'Patricia',
            'location': 'Union Square',
            'start': 16 * 60 + 30, # 990
            'end': 20 * 60,        # 1200
            'duration': 120
        },
        {
            'index': 9,
            'name': 'Karen',
            'location': 'Sunset District',
            'start': 16 * 60 + 30, # 990
            'end': 22 * 60,        # 1320
            'duration': 105
        }
    ]

    distance_data = [
        ('Financial District', "Fisherman's Wharf", 10),
        ('Financial District', 'Presidio', 22),
        ('Financial District', 'Bayview', 19),
        ('Financial District', 'Haight-Ashbury', 19),
        ('Financial District', 'Russian Hill', 11),
        ('Financial District', 'The Castro', 20),
        ('Financial District', 'Marina District', 15),
        ('Financial District', 'Richmond District', 21),
        ('Financial District', 'Union Square', 9),
        ('Financial District', 'Sunset District', 30),
        ("Fisherman's Wharf", 'Financial District', 11),
        ("Fisherman's Wharf", 'Presidio', 17),
        ("Fisherman's Wharf", 'Bayview', 26),
        ("Fisherman's Wharf", 'Haight-Ashbury', 22),
        ("Fisherman's Wharf", 'Russian Hill', 7),
        ("Fisherman's Wharf", 'The Castro', 27),
        ("Fisherman's Wharf", 'Marina District', 9),
        ("Fisherman's Wharf", 'Richmond District', 18),
        ("Fisherman's Wharf", 'Union Square', 13),
        ("Fisherman's Wharf", 'Sunset District', 27),
        ('Presidio', 'Financial District', 23),
        ('Presidio', "Fisherman's Wharf", 19),
        ('Presidio', 'Bayview', 31),
        ('Presidio', 'Haight-Ashbury', 15),
        ('Presidio', 'Russian Hill', 14),
        ('Presidio', 'The Castro', 21),
        ('Presidio', 'Marina District', 11),
        ('Presidio', 'Richmond District', 7),
        ('Presidio', 'Union Square', 22),
        ('Presidio', 'Sunset District', 15),
        ('Bayview', 'Financial District', 19),
        ('Bayview', "Fisherman's Wharf", 25),
        ('Bayview', 'Presidio', 32),
        ('Bayview', 'Haight-Ashbury', 19),
        ('Bayview', 'Russian Hill', 23),
        ('Bayview', 'The Castro', 19),
        ('Bayview', 'Marina District', 27),
        ('Bayview', 'Richmond District', 25),
        ('Bayview', 'Union Square', 18),
        ('Bayview', 'Sunset District', 23),
        ('Haight-Ashbury', 'Financial District', 21),
        ('Haight-Ashbury', "Fisherman's Wharf", 23),
        ('Haight-Ashbury', 'Presidio', 15),
        ('Haight-Ashbury', 'Bayview', 18),
        ('Haight-Ashbury', 'Russian Hill', 17),
        ('Haight-Ashbury', 'The Castro', 6),
        ('Haight-Ashbury', 'Marina District', 17),
        ('Haight-Ashbury', 'Richmond District', 10),
        ('Haight-Ashbury', 'Union Square', 19),
        ('Haight-Ashbury', 'Sunset District', 15),
        ('Russian Hill', 'Financial District', 11),
        ('Russian Hill', "Fisherman's Wharf", 7),
        ('Russian Hill', 'Presidio', 14),
        ('Russian Hill', 'Bayview', 23),
        ('Russian Hill', 'Haight-Ashbury', 17),
        ('Russian Hill', 'The Castro', 21),
        ('Russian Hill', 'Marina District', 7),
        ('Russian Hill', 'Richmond District', 14),
        ('Russian Hill', 'Union Square', 10),
        ('Russian Hill', 'Sunset District', 23),
        ('The Castro', 'Financial District', 21),
        ('The Castro', "Fisherman's Wharf", 24),
        ('The Castro', 'Presidio', 20),
        ('The Castro', 'Bayview', 19),
        ('The Castro', 'Haight-Ashbury', 6),
        ('The Castro', 'Russian Hill', 18),
        ('The Castro', 'Marina District', 21),
        ('The Castro', 'Richmond District', 16),
        ('The Castro', 'Union Square', 19),
        ('The Castro', 'Sunset District', 17),
        ('Marina District', 'Financial District', 17),
        ('Marina District', "Fisherman's Wharf", 10),
        ('Marina District', 'Presidio', 10),
        ('Marina District', 'Bayview', 27),
        ('Marina District', 'Haight-Ashbury', 16),
        ('Marina District', 'Russian Hill', 8),
        ('Marina District', 'The Castro', 22),
        ('Marina District', 'Richmond District', 11),
        ('Marina District', 'Union Square', 16),
        ('Marina District', 'Sunset District', 19),
        ('Richmond District', 'Financial District', 22),
        ('Richmond District', "Fisherman's Wharf", 18),
        ('Richmond District', 'Presidio', 7),
        ('Richmond District', 'Bayview', 27),
        ('Richmond District', 'Haight-Ashbury', 10),
        ('Richmond District', 'Russian Hill', 13),
        ('Richmond District', 'The Castro', 16),
        ('Richmond District', 'Marina District', 9),
        ('Richmond District', 'Union Square', 21),
        ('Richmond District', 'Sunset District', 11),
        ('Union Square', 'Financial District', 9),
        ('Union Square', "Fisherman's Wharf", 15),
        ('Union Square', 'Presidio', 24),
        ('Union Square', 'Bayview', 15),
        ('Union Square', 'Haight-Ashbury', 18),
        ('Union Square', 'Russian Hill', 13),
        ('Union Square', 'The Castro', 17),
        ('Union Square', 'Marina District', 18),
        ('Union Square', 'Richmond District', 20),
        ('Union Square', 'Sunset District', 27),
        ('Sunset District', 'Financial District', 30),
        ('Sunset District', "Fisherman's Wharf", 29),
        ('Sunset District', 'Presidio', 16),
        ('Sunset District', 'Bayview', 22),
        ('Sunset District', 'Haight-Ashbury', 15),
        ('Sunset District', 'Russian Hill', 24),
        ('Sunset District', 'The Castro', 17),
        ('Sunset District', 'Marina District', 21),
        ('Sunset District', 'Richmond District', 12),
        ('Sunset District', 'Union Square', 30),
    ]

    distance = {}
    for loc1, loc2, dist in distance_data:
        if loc1 not in distance:
            distance[loc1] = {}
        distance[loc1][loc2] = dist

    # Initial state
    start_location = 'Financial District'
    start_time = 9 * 60  # 540 minutes
    initial_mask = 0
    initial_path = []

    # Priority queue: (-num_met, current_time, current_location, friends_mask, path)
    heap = []
    heapq.heappush(heap, (0, start_time, start_location, initial_mask, initial_path))

    # Memoization: (location, mask) -> earliest_time
    memo = {}

    best_solution = None

    while heap:
        neg_num_met, current_time, current_loc, mask, path = heapq.heappop(heap)
        num_met = -neg_num_met

        # Check if this state is dominated
        key = (current_loc, mask)
        if key in memo:
            if memo[key] <= current_time:
                continue
        memo[key] = current_time

        # Update best solution if needed
        if best_solution is None or num_met > len(best_solution['itinerary']) or \
           (num_met == len(best_solution['itinerary']) and current_time < best_solution['end_time']):
            best_solution = {
                'itinerary': path.copy(),
                'end_time': current_time
            }

        # Try to meet each friend not yet met
        for friend in friends:
            if mask & (1 << friend['index']):
                continue  # already met
            friend_loc = friend['location']
            friend_start = friend['start']
            friend_end = friend['end']
            friend_duration = friend['duration']

            # Calculate travel time
            if current_loc not in distance or friend_loc not in distance[current_loc]:
                continue  # no travel time available (shouldn't happen)
            travel_time = distance[current_loc][friend_loc]
            arrival_time = current_time + travel_time

            # Determine possible start time
            possible_start = max(arrival_time, friend_start)
            if possible_start + friend_duration > friend_end:
                continue  # not enough time

            new_time = possible_start + friend_duration
            new_mask = mask | (1 << friend['index'])
            new_path = path + [{
                'action': 'meet',
                'location': friend_loc,
                'person': friend['name'],
                'start_time': minutes_to_time(possible_start),
                'end_time': minutes_to_time(new_time)
            }]

            # Check if this new state is better than existing ones
            new_key = (friend_loc, new_mask)
            if new_key not in memo or memo[new_key] > new_time:
                memo[new_key] = new_time
                heapq.heappush(heap, (- (num_met + 1), new_time, friend_loc, new_mask, new_path))

    # Output the best solution
    if best_solution is None:
        print(json.dumps({"itinerary": []}))
    else:
        print(json.dumps({"itinerary": best_solution['itinerary']}))

if __name__ == "__main__":
    main()