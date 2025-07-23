import itertools

def min_to_time(minutes):
    total_minutes = minutes
    hours = total_minutes // 60
    mins = total_minutes % 60
    total_hours = 9 + hours
    return f"{total_hours:02d}:{mins:02d}"

travel_dict = {
    'Nob Hill': {
        'Richmond District': 14,
        'Financial District': 9,
        'North Beach': 8,
        'The Castro': 17,
        'Golden Gate Park': 17
    },
    'Richmond District': {
        'Nob Hill': 17,
        'Financial District': 22,
        'North Beach': 18,
        'The Castro': 16,
        'Golden Gate Park': 9
    },
    'Financial District': {
        'Nob Hill': 8,
        'Richmond District': 21,
        'North Beach': 7,
        'The Castro': 23,
        'Golden Gate Park': 23
    },
    'North Beach': {
        'Nob Hill': 7,
        'Richmond District': 18,
        'Financial District': 8,
        'The Castro': 22,
        'Golden Gate Park': 22
    },
    'The Castro': {
        'Nob Hill': 16,
        'Richmond District': 16,
        'Financial District': 20,
        'North Beach': 20,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Nob Hill': 20,
        'Richmond District': 7,
        'Financial District': 26,
        'North Beach': 24,
        'The Castro': 13
    }
}

friends_data = [
    {'name': 'Emily', 'location': 'Richmond District', 'start_avail': 600, 'end_avail': 720, 'min_time': 15},
    {'name': 'Margaret', 'location': 'Financial District', 'start_avail': 450, 'end_avail': 675, 'min_time': 75},
    {'name': 'Ronald', 'location': 'North Beach', 'start_avail': 570, 'end_avail': 630, 'min_time': 45},
    {'name': 'Deborah', 'location': 'The Castro', 'start_avail': 285, 'end_avail': 735, 'min_time': 90},
    {'name': 'Jeffrey', 'location': 'Golden Gate Park', 'start_avail': 135, 'end_avail': 330, 'min_time': 120}
]

def simulate_order(order):
    current_location = 'Nob Hill'
    current_time = 0
    schedule = []
    for friend in order:
        loc = friend['location']
        tt = travel_dict[current_location][loc]
        arrival_time = current_time + tt
        start_meeting = max(arrival_time, friend['start_avail'])
        end_meeting = start_meeting + friend['min_time']
        if end_meeting > friend['end_avail']:
            return None
        schedule.append((friend['name'], start_meeting, end_meeting))
        current_location = loc
        current_time = end_meeting
    return schedule

def main():
    n = len(friends_data)
    for k in range(n, 0, -1):
        for subset in itertools.combinations(friends_data, k):
            for perm in itertools.permutations(subset):
                result = simulate_order(perm)
                if result is not None:
                    itinerary = []
                    for name, start_min, end_min in result:
                        start_str = min_to_time(start_min)
                        end_str = min_to_time(end_min)
                        itinerary.append({
                            "action": "meet",
                            "person": name,
                            "start_time": start_str,
                            "end_time": end_str
                        })
                    return {"itinerary": itinerary}
    return {"itinerary": []}

if __name__ == "__main__":
    solution = main()
    print("SOLUTION:")
    print(solution)