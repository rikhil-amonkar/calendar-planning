import heapq
import json

def main():
    friends = [
        {'name': 'Jessica', 'location': 'Russian Hill', 'start_time': 540, 'end_time': 900, 'duration': 120},
        {'name': 'John', 'location': 'North Beach', 'start_time': 585, 'end_time': 1020, 'duration': 15},
        {'name': 'Nancy', 'location': 'Nob Hill', 'start_time': 585, 'end_time': 660, 'duration': 45},
        {'name': 'Rebecca', 'location': 'Sunset District', 'start_time': 525, 'end_time': 900, 'duration': 75},
        {'name': 'Jason', 'location': 'Marina District', 'start_time': 915, 'end_time': 1305, 'duration': 120},
        {'name': 'Karen', 'location': 'Chinatown', 'start_time': 1005, 'end_time': 1140, 'duration': 75},
        {'name': 'Sarah', 'location': 'Pacific Heights', 'start_time': 1050, 'end_time': 1095, 'duration': 45},
        {'name': 'Amanda', 'location': 'The Castro', 'start_time': 1200, 'end_time': 1275, 'duration': 60},
        {'name': 'Kevin', 'location': 'Mission District', 'start_time': 1245, 'end_time': 1305, 'duration': 60},
        {'name': 'Mark', 'location': "Fisherman's Wharf", 'start_time': 915, 'end_time': 1200, 'duration': 90},
    ]

    travel_times = {
        ('Union Square', 'Mission District'): 14,
        ('Union Square', "Fisherman's Wharf"): 15,
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Sunset District'): 27,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', "Fisherman's Wharf"): 22,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Sunset District'): 24,
        ("Fisherman's Wharf", 'Union Square'): 13,
        ("Fisherman's Wharf", 'Mission District'): 22,
        ("Fisherman's Wharf", 'Russian Hill'): 7,
        ("Fisherman's Wharf", 'Marina District'): 9,
        ("Fisherman's Wharf", 'North Beach'): 6,
        ("Fisherman's Wharf", 'Chinatown'): 12,
        ("Fisherman's Wharf", 'Pacific Heights'): 12,
        ("Fisherman's Wharf", 'The Castro'): 27,
        ("Fisherman's Wharf", 'Nob Hill'): 11,
        ("Fisherman's Wharf", 'Sunset District'): 27,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', "Fisherman's Wharf"): 7,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Sunset District'): 23,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', "Fisherman's Wharf"): 10,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Sunset District'): 19,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', "Fisherman's Wharf"): 5,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Sunset District'): 27,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Mission District'): 17,
        ('Chinatown', "Fisherman's Wharf"): 8,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Sunset District'): 29,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', "Fisherman's Wharf"): 13,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Sunset District'): 21,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', "Fisherman's Wharf"): 24,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Sunset District'): 17,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', "Fisherman's Wharf"): 10,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Sunset District'): 24,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Mission District'): 25,
        ('Sunset District', "Fisherman's Wharf"): 29,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Nob Hill'): 27,
    }

    initial_location = 'Union Square'
    initial_time = 540  # 9:00 AM in minutes since midnight
    num_friends = len(friends)

    heap = []
    heapq.heappush(heap, (0, initial_time, initial_location, 0))  # (neg_num_friends, time, location, bitmask)

    dp = {}
    dp_key = (initial_location, 0)
    dp[dp_key] = initial_time

    prev = {}

    while heap:
        neg_num_friends, current_time, current_location, current_bitmask = heapq.heappop(heap)
        current_num_friends = -neg_num_friends

        if (current_location, current_bitmask) not in dp or dp[(current_location, current_bitmask)] < current_time:
            continue

        for i in range(num_friends):
            if not (current_bitmask & (1 << i)):
                friend = friends[i]
                friend_location = friend['location']
                friend_start = friend['start_time']
                friend_end = friend['end_time']
                duration = friend['duration']

                travel_time = travel_times.get((current_location, friend_location), None)
                if travel_time is None:
                    continue

                arrival_time_at_friend = current_time + travel_time
                meeting_start = max(arrival_time_at_friend, friend_start)
                meeting_end = meeting_start + duration

                if meeting_end > friend_end:
                    continue

                new_bitmask = current_bitmask | (1 << i)
                new_location = friend_location
                new_time = meeting_end

                new_dp_key = (new_location, new_bitmask)
                if new_dp_key not in dp or new_time < dp[new_dp_key]:
                    dp[new_dp_key] = new_time
                    heapq.heappush(heap, (-bin(new_bitmask).count('1'), new_time, new_location, new_bitmask))
                    prev[new_dp_key] = (current_location, current_bitmask, i)

    best_bitmask = 0
    best_location = initial_location
    max_friends = 0
    for (loc, bitmask), time in dp.items():
        count = bin(bitmask).count('1')
        if count > max_friends:
            max_friends = count
            best_bitmask = bitmask
            best_location = loc

    itinerary = []
    current_state = (best_location, best_bitmask)
    while current_state in prev:
        prev_location, prev_bitmask, friend_index = prev[current_state]
        friend = friends[friend_index]
        prev_time = dp[(prev_location, prev_bitmask)]
        travel_time = travel_times.get((prev_location, friend['location']), 0)
        arrival_at_friend_loc = prev_time + travel_time
        meeting_start = max(arrival_at_friend_loc, friend['start_time'])
        meeting_end = meeting_start + friend['duration']
        start_h, start_m = divmod(meeting_start, 60)
        end_h, end_m = divmod(meeting_end, 60)
        start_time_str = f"{start_h}:{start_m:02d}"
        end_time_str = f"{end_h}:{end_m:02d}"
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_time_str,
            "end_time": end_time_str
        })
        current_state = (prev_location, prev_bitmask)

    itinerary.reverse()

    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()