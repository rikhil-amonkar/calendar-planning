import heapq
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends_order = ['Mark', 'Karen', 'Barbara', 'Nancy', 'David', 'Linda', 'Kevin', 'Matthew', 'Andrew']
    friends_data = [
        {
            'name': 'Mark',
            'location': 'Marina District',
            'available_start': 1125,
            'available_end': 1260,
            'required_duration': 90,
            'latest_start': 1170
        },
        {
            'name': 'Karen',
            'location': 'Financial District',
            'available_start': 570,
            'available_end': 765,
            'required_duration': 90,
            'latest_start': 675
        },
        {
            'name': 'Barbara',
            'location': 'Alamo Square',
            'available_start': 600,
            'available_end': 1170,
            'required_duration': 90,
            'latest_start': 1080
        },
        {
            'name': 'Nancy',
            'location': 'Golden Gate Park',
            'available_start': 1005,
            'available_end': 1200,
            'required_duration': 105,
            'latest_start': 1095
        },
        {
            'name': 'David',
            'location': 'The Castro',
            'available_start': 540,
            'available_end': 1080,
            'required_duration': 120,
            'latest_start': 960
        },
        {
            'name': 'Linda',
            'location': 'Bayview',
            'available_start': 1095,
            'available_end': 1185,
            'required_duration': 45,
            'latest_start': 1140
        },
        {
            'name': 'Kevin',
            'location': 'Sunset District',
            'available_start': 600,
            'available_end': 1065,
            'required_duration': 120,
            'latest_start': 945
        },
        {
            'name': 'Matthew',
            'location': 'Haight-Ashbury',
            'available_start': 615,
            'available_end': 930,
            'required_duration': 45,
            'latest_start': 885
        },
        {
            'name': 'Andrew',
            'location': 'Nob Hill',
            'available_start': 705,
            'available_end': 1005,
            'required_duration': 105,
            'latest_start': 900
        }
    ]
    travel_times = {
        'Russian Hill': {
            'Marina District': 7,
            'Financial District': 11,
            'Alamo Square': 15,
            'Golden Gate Park': 21,
            'The Castro': 21,
            'Bayview': 23,
            'Sunset District': 23,
            'Haight-Ashbury': 17,
            'Nob Hill': 5
        },
        'Marina District': {
            'Russian Hill': 8,
            'Financial District': 17,
            'Alamo Square': 15,
            'Golden Gate Park': 18,
            'The Castro': 22,
            'Bayview': 27,
            'Sunset District': 19,
            'Haight-Ashbury': 16,
            'Nob Hill': 12
        },
        'Financial District': {
            'Russian Hill': 11,
            'Marina District': 15,
            'Alamo Square': 17,
            'Golden Gate Park': 23,
            'The Castro': 20,
            'Bayview': 19,
            'Sunset District': 30,
            'Haight-Ashbury': 19,
            'Nob Hill': 8
        },
        'Alamo Square': {
            'Russian Hill': 13,
            'Marina District': 15,
            'Financial District': 17,
            'Golden Gate Park': 9,
            'The Castro': 8,
            'Bayview': 16,
            'Sunset District': 16,
            'Haight-Ashbury': 5,
            'Nob Hill': 11
        },
        'Golden Gate Park': {
            'Russian Hill': 19,
            'Marina District': 16,
            'Financial District': 26,
            'Alamo Square': 9,
            'The Castro': 13,
            'Bayview': 23,
            'Sunset District': 10,
            'Haight-Ashbury': 7,
            'Nob Hill': 20
        },
        'The Castro': {
            'Russian Hill': 18,
            'Marina District': 21,
            'Financial District': 21,
            'Alamo Square': 8,
            'Golden Gate Park': 11,
            'Bayview': 19,
            'Sunset District': 17,
            'Haight-Ashbury': 6,
            'Nob Hill': 16
        },
        'Bayview': {
            'Russian Hill': 23,
            'Marina District': 27,
            'Financial District': 19,
            'Alamo Square': 16,
            'Golden Gate Park': 22,
            'The Castro': 19,
            'Sunset District': 23,
            'Haight-Ashbury': 19,
            'Nob Hill': 20
        },
        'Sunset District': {
            'Russian Hill': 24,
            'Marina District': 21,
            'Financial District': 30,
            'Alamo Square': 17,
            'Golden Gate Park': 11,
            'The Castro': 17,
            'Bayview': 22,
            'Haight-Ashbury': 15,
            'Nob Hill': 27
        },
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Marina District': 17,
            'Financial District': 21,
            'Alamo Square': 5,
            'Golden Gate Park': 7,
            'The Castro': 6,
            'Bayview': 18,
            'Sunset District': 15,
            'Nob Hill': 15
        },
        'Nob Hill': {
            'Russian Hill': 5,
            'Marina District': 11,
            'Financial District': 9,
            'Alamo Square': 11,
            'Golden Gate Park': 17,
            'The Castro': 17,
            'Bayview': 19,
            'Sunset District': 24,
            'Haight-Ashbury': 13
        }
    }

    initial_time = 540  # 9:00 AM
    initial_location = 'Russian Hill'
    initial_mask = 0
    initial_itinerary = []

    heap = []
    heapq.heappush(heap, (0, initial_time, initial_location, initial_mask, initial_itinerary))
    memo = {}

    best_itinerary = None

    while heap:
        neg_num_friends, current_time, current_location, mask, itinerary = heapq.heappop(heap)
        num_friends = -neg_num_friends

        key = (current_location, current_time)
        if key in memo and memo[key] >= num_friends:
            continue
        memo[key] = num_friends

        if best_itinerary is None or len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary.copy()

        for friend_idx in range(len(friends_data)):
            if not (mask & (1 << friend_idx)):
                friend = friends_data[friend_idx]
                friend_loc = friend['location']
                travel_time_minutes = travel_times.get(current_location, {}).get(friend_loc, None)
                if travel_time_minutes is None:
                    continue
                arrival_time = current_time + travel_time_minutes
                earliest_start = max(arrival_time, friend['available_start'])
                latest_start = friend['latest_start']
                if earliest_start > latest_start:
                    continue
                meeting_end_time = earliest_start + friend['required_duration']
                new_time = meeting_end_time
                new_location = friend_loc
                new_mask = mask | (1 << friend_idx)
                new_neg_num_friends = -bin(new_mask).count('1')

                new_itinerary = itinerary + [{
                    'action': 'meet',
                    'location': friend_loc,
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(earliest_start),
                    'end_time': minutes_to_time_str(meeting_end_time)
                }]

                if meeting_end_time > friend['available_end']:
                    continue

                new_key = (new_location, new_time)
                if new_key in memo and memo[new_key] >= bin(new_mask).count('1'):
                    continue
                memo[new_key] = bin(new_mask).count('1')

                heapq.heappush(heap, (new_neg_num_friends, new_time, new_location, new_mask, new_itinerary))

    if best_itinerary:
        best_itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": best_itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()