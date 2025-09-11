import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'name': 'Jessica',
            'location': 'Russian Hill',
            'start_time': 9 * 60,
            'end_time': 15 * 60,
            'required_duration': 120
        },
        {
            'name': 'John',
            'location': 'North Beach',
            'start_time': 9 * 60 + 45,
            'end_time': 18 * 60,
            'required_duration': 15
        },
        {
            'name': 'Nancy',
            'location': 'Nob Hill',
            'start_time': 9 * 60 + 45,
            'end_time': 13 * 60,
            'required_duration': 45
        },
        {
            'name': 'Rebecca',
            'location': 'Sunset District',
            'start_time': 8 * 60 + 45,
            'end_time': 15 * 60,
            'required_duration': 75
        },
        {
            'name': 'Jason',
            'location': 'Marina District',
            'start_time': 15 * 60 + 15,
            'end_time': 21 * 60 + 45,
            'required_duration': 120
        },
        {
            'name': 'Karen',
            'location': 'Chinatown',
            'start_time': 16 * 60 + 45,
            'end_time': 19 * 60,
            'required_duration': 75
        },
        {
            'name': 'Sarah',
            'location': 'Pacific Heights',
            'start_time': 17 * 60 + 30,
            'end_time': 18 * 60 + 15,
            'required_duration': 45
        },
        {
            'name': 'Mark',
            'location': "Fisherman's Wharf",
            'start_time': 17 * 60 + 15,
            'end_time': 20 * 60,
            'required_duration': 90
        },
        {
            'name': 'Kevin',
            'location': 'Mission District',
            'start_time': 20 * 60 + 45,
            'end_time': 21 * 60 + 45,
            'required_duration': 60
        },
        {
            'name': 'Amanda',
            'location': 'The Castro',
            'start_time': 20 * 60,
            'end_time': 21 * 60 + 15,
            'required_duration': 60
        }
    ]

    travel_times = {
        'Union Square': {
            'Mission District': 14,
            "Fisherman's Wharf": 15,
            'Russian Hill': 13,
            'Marina District': 18,
            'North Beach': 10,
            'Chinatown': 7,
            'Pacific Heights': 15,
            'The Castro': 17,
            'Nob Hill': 9,
            'Sunset District': 27
        },
        'Mission District': {
            'Union Square': 15,
            "Fisherman's Wharf": 22,
            'Russian Hill': 15,
            'Marina District': 19,
            'North Beach': 17,
            'Chinatown': 16,
            'Pacific Heights': 16,
            'The Castro': 7,
            'Nob Hill': 12,
            'Sunset District': 24
        },
        "Fisherman's Wharf": {
            'Union Square': 13,
            'Mission District': 22,
            'Russian Hill': 7,
            'Marina District': 9,
            'North Beach': 6,
            'Chinatown': 12,
            'Pacific Heights': 12,
            'The Castro': 27,
            'Nob Hill': 11,
            'Sunset District': 27
        },
        'Russian Hill': {
            'Union Square': 10,
            'Mission District': 16,
            "Fisherman's Wharf": 7,
            'Marina District': 7,
            'North Beach': 5,
            'Chinatown': 9,
            'Pacific Heights': 7,
            'The Castro': 21,
            'Nob Hill': 5,
            'Sunset District': 23
        },
        'Marina District': {
            'Union Square': 16,
            'Mission District': 20,
            "Fisherman's Wharf": 10,
            'Russian Hill': 8,
            'North Beach': 11,
            'Chinatown': 15,
            'Pacific Heights': 7,
            'The Castro': 22,
            'Nob Hill': 12,
            'Sunset District': 19
        },
        'North Beach': {
            'Union Square': 7,
            'Mission District': 18,
            "Fisherman's Wharf": 5,
            'Russian Hill': 4,
            'Marina District': 9,
            'Chinatown': 6,
            'Pacific Heights': 8,
            'The Castro': 23,
            'Nob Hill': 7,
            'Sunset District': 27
        },
        'Chinatown': {
            'Union Square': 7,
            'Mission District': 17,
            "Fisherman's Wharf": 8,
            'Russian Hill': 7,
            'Marina District': 12,
            'North Beach': 3,
            'Pacific Heights': 10,
            'The Castro': 22,
            'Nob Hill': 9,
            'Sunset District': 29
        },
        'Pacific Heights': {
            'Union Square': 12,
            'Mission District': 15,
            "Fisherman's Wharf": 13,
            'Russian Hill': 7,
            'Marina District': 6,
            'North Beach': 9,
            'Chinatown': 11,
            'The Castro': 16,
            'Nob Hill': 8,
            'Sunset District': 21
        },
        'The Castro': {
            'Union Square': 19,
            'Mission District': 7,
            "Fisherman's Wharf": 24,
            'Russian Hill': 18,
            'Marina District': 21,
            'North Beach': 20,
            'Chinatown': 22,
            'Pacific Heights': 16,
            'Nob Hill': 16,
            'Sunset District': 17
        },
        'Nob Hill': {
            'Union Square': 7,
            'Mission District': 13,
            "Fisherman's Wharf": 10,
            'Russian Hill': 5,
            'Marina District': 11,
            'North Beach': 8,
            'Chinatown': 6,
            'Pacific Heights': 8,
            'The Castro': 17,
            'Sunset District': 24
        },
        'Sunset District': {
            'Union Square': 30,
            'Mission District': 25,
            "Fisherman's Wharf": 29,
            'Russian Hill': 24,
            'Marina District': 21,
            'North Beach': 28,
            'Chinatown': 30,
            'Pacific Heights': 21,
            'The Castro': 17,
            'Nob Hill': 27
        }
    }

    memo = {}

    def dfs(current_time, current_location, visited_mask):
        key = (current_time, current_location, visited_mask)
        if key in memo:
            return memo[key]

        max_count = 0
        best_itinerary = []

        for idx in range(len(friends)):
            if not (visited_mask & (1 << idx)):
                friend = friends[idx]
                if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
                    continue
                travel_time = travel_times[current_location][friend['location']]
                arrival_time = current_time + travel_time
                required_duration = friend['required_duration']
                if arrival_time >= friend['start_time'] and (arrival_time + required_duration) <= friend['end_time']:
                    new_time = arrival_time + required_duration
                    new_mask = visited_mask | (1 << idx)
                    count, sub_itinerary = dfs(new_time, friend['location'], new_mask)
                    count += 1
                    if count > max_count:
                        max_count = count
                        new_meeting = {
                            'action': 'meet',
                            'location': friend['location'],
                            'person': friend['name'],
                            'start_time': minutes_to_time(arrival_time),
                            'end_time': minutes_to_time(arrival_time + required_duration)
                        }
                        best_itinerary = [new_meeting] + sub_itinerary

        memo[key] = (max_count, best_itinerary)
        return (max_count, best_itinerary)

    max_count, best_itinerary = dfs(540, 'Union Square', 0)

    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()