import heapq
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define friends with their constraints
    friends = [
        {
            'name': 'Matthew',
            'location': 'Presidio',
            'start_time': 8 * 60 + 15,  # 8:15 AM
            'end_time': 9 * 60 + 0,     # 9:00 AM
            'required_duration': 15,
        },
        {
            'name': 'Richard',
            'location': "Fisherman's Wharf",
            'start_time': 11 * 60 + 0,  # 11:00 AM
            'end_time': 12 * 60 + 45,   # 12:45 PM
            'required_duration': 60,
        },
        {
            'name': 'Elizabeth',
            'location': 'Nob Hill',
            'start_time': 11 * 60 + 45, # 11:45 AM
            'end_time': 18 * 60 + 30,   # 6:30 PM
            'required_duration': 75,
        },
        {
            'name': 'Brian',
            'location': 'North Beach',
            'start_time': 13 * 60 + 0,  # 1:00 PM
            'end_time': 19 * 60 + 0,    # 7:00 PM
            'required_duration': 90,
        },
        {
            'name': 'Ashley',
            'location': 'Haight-Ashbury',
            'start_time': 15 * 60 + 0,  # 3:00 PM
            'end_time': 20 * 60 + 30,   # 8:30 PM
            'required_duration': 90,
        },
        {
            'name': 'Jessica',
            'location': 'Golden Gate Park',
            'start_time': 20 * 60 + 0,  # 8:00 PM
            'end_time': 21 * 60 + 45,   # 9:45 PM
            'required_duration': 105,
        },
        {
            'name': 'Deborah',
            'location': 'Union Square',
            'start_time': 17 * 60 + 30, # 5:30 PM
            'end_time': 22 * 60 + 0,    # 10:00 PM
            'required_duration': 60,
        },
        {
            'name': 'Kimberly',
            'location': 'Alamo Square',
            'start_time': 17 * 60 + 30, # 5:30 PM
            'end_time': 21 * 60 + 15,   # 9:15 PM
            'required_duration': 45,
        },
        {
            'name': 'Kenneth',
            'location': 'Chinatown',
            'start_time': 13 * 60 + 45, # 1:45 PM
            'end_time': 19 * 60 + 30,   # 7:30 PM
            'required_duration': 105,
        },
        {
            'name': 'Anthony',
            'location': 'Pacific Heights',
            'start_time': 14 * 60 + 15, # 2:15 PM
            'end_time': 16 * 60 + 0,    # 4:00 PM
            'required_duration': 30,
        },
    ]

    # Precompute LAT for each friend
    for f in friends:
        f['LAT'] = f['end_time'] - f['required_duration']

    # Define travel times between locations
    travel_times = {
        'Bayview': {
            'North Beach': 22,
            "Fisherman's Wharf": 25,
            'Haight-Ashbury': 19,
            'Nob Hill': 20,
            'Golden Gate Park': 22,
            'Union Square': 18,
            'Alamo Square': 16,
            'Presidio': 32,
            'Chinatown': 19,
            'Pacific Heights': 23,
        },
        'North Beach': {
            'Bayview': 25,
            "Fisherman's Wharf": 5,
            'Haight-Ashbury': 18,
            'Nob Hill': 7,
            'Golden Gate Park': 22,
            'Union Square': 7,
            'Alamo Square': 16,
            'Presidio': 17,
            'Chinatown': 6,
            'Pacific Heights': 8,
        },
        "Fisherman's Wharf": {
            'Bayview': 26,
            'North Beach': 6,
            'Haight-Ashbury': 22,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Union Square': 13,
            'Alamo Square': 21,
            'Presidio': 17,
            'Chinatown': 12,
            'Pacific Heights': 12,
        },
        'Haight-Ashbury': {
            'Bayview': 18,
            'North Beach': 19,
            "Fisherman's Wharf": 23,
            'Nob Hill': 15,
            'Golden Gate Park': 7,
            'Union Square': 19,
            'Alamo Square': 5,
            'Presidio': 15,
            'Chinatown': 19,
            'Pacific Heights': 12,
        },
        'Nob Hill': {
            'Bayview': 19,
            'North Beach': 8,
            "Fisherman's Wharf": 10,
            'Haight-Ashbury': 13,
            'Golden Gate Park': 17,
            'Union Square': 7,
            'Alamo Square': 11,
            'Presidio': 17,
            'Chinatown': 6,
            'Pacific Heights': 8,
        },
        'Golden Gate Park': {
            'Bayview': 23,
            'North Beach': 23,
            "Fisherman's Wharf": 24,
            'Haight-Ashbury': 7,
            'Nob Hill': 20,
            'Union Square': 22,
            'Alamo Square': 9,
            'Presidio': 11,
            'Chinatown': 23,
            'Pacific Heights': 16,
        },
        'Union Square': {
            'Bayview': 15,
            'North Beach': 10,
            "Fisherman's Wharf": 15,
            'Haight-Ashbury': 18,
            'Nob Hill': 9,
            'Golden Gate Park': 22,
            'Alamo Square': 15,
            'Presidio': 24,
            'Chinatown': 7,
            'Pacific Heights': 15,
        },
        'Alamo Square': {
            'Bayview': 16,
            'North Beach': 15,
            "Fisherman's Wharf": 19,
            'Haight-Ashbury': 5,
            'Nob Hill': 11,
            'Golden Gate Park': 9,
            'Union Square': 14,
            'Presidio': 17,
            'Chinatown': 15,
            'Pacific Heights': 10,
        },
        'Presidio': {
            'Bayview': 31,
            'North Beach': 18,
            "Fisherman's Wharf": 19,
            'Haight-Ashbury': 15,
            'Nob Hill': 18,
            'Golden Gate Park': 12,
            'Union Square': 22,
            'Alamo Square': 19,
            'Chinatown': 21,
            'Pacific Heights': 11,
        },
        'Chinatown': {
            'Bayview': 20,
            'North Beach': 3,
            "Fisherman's Wharf": 8,
            'Haight-Ashbury': 19,
            'Nob Hill': 9,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'Alamo Square': 17,
            'Presidio': 19,
            'Pacific Heights': 10,
        },
        'Pacific Heights': {
            'Bayview': 22,
            'North Beach': 9,
            "Fisherman's Wharf": 13,
            'Haight-Ashbury': 11,
            'Nob Hill': 8,
            'Golden Gate Park': 15,
            'Union Square': 12,
            'Alamo Square': 10,
            'Presidio': 11,
            'Chinatown': 11,
        },
    }

    # Initial state
    initial_time = 9 * 60  # 9:00 AM
    initial_location = 'Bayview'
    initial_bitmask = 0
    initial_itinerary = []

    # Priority queue: (current_time, -bitmask_length, bitmask, current_location, itinerary)
    heap = []
    heapq.heappush(heap, (initial_time, 0, initial_bitmask, initial_location, initial_itinerary))

    # best_states: key is (bitmask, location), value is the earliest current_time to reach it
    best_states = {}
    best_states[(initial_bitmask, initial_location)] = initial_time

    best_itinerary = []

    while heap:
        current_time, neg_bitmask_len, bitmask, current_location, itinerary = heapq.heappop(heap)

        # Check if this state is obsolete (a better state already processed)
        if best_states.get((bitmask, current_location), float('inf')) < current_time:
            continue

        # Update best itinerary if this one is better
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary.copy()

        # Try to visit each friend not yet visited
        for i in range(len(friends)):
            if not (bitmask & (1 << i)):
                friend = friends[i]
                friend_loc = friend['location']
                travel_time = travel_times.get(current_location, {}).get(friend_loc, float('inf'))
                if travel_time == float('inf'):
                    continue  # No travel time defined between current and friend's location (shouldn't happen)

                # Calculate arrival time, considering waiting if needed
                arrival_time = max(current_time + travel_time, friend['start_time'])
                if arrival_time > friend['LAT']:
                    continue  # Can't visit this friend

                new_time = arrival_time + friend['required_duration']
                new_bitmask = bitmask | (1 << i)
                new_location = friend_loc
                new_itinerary = itinerary + [{
                    'action': 'meet',
                    'location': friend_loc,
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(arrival_time),
                    'end_time': minutes_to_time_str(new_time),
                }]

                # Check if this new state is better than existing ones
                state_key = (new_bitmask, new_location)
                if (state_key not in best_states) or (new_time < best_states[state_key]):
                    best_states[state_key] = new_time
                    new_bitmask_len = bin(new_bitmask).count('1')
                    heapq.heappush(heap, (new_time, -new_bitmask_len, new_bitmask, new_location, new_itinerary))

    # Output the best itinerary found
    print(json.dumps({"itinerary": best_itinerary}, indent=2))

if __name__ == '__main__':
    main()