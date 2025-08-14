import json
from functools import lru_cache

def main():
    # Define friends' data
    friends_data = [
        {
            'name': 'Emily',
            'location': 'Pacific Heights',
            'start': '9:15',
            'end': '13:45',
            'duration': 120
        },
        {
            'name': 'Helen',
            'location': 'North Beach',
            'start': '13:45',
            'end': '18:45',
            'duration': 30
        },
        {
            'name': 'Kimberly',
            'location': 'Golden Gate Park',
            'start': '18:45',
            'end': '21:15',
            'duration': 75
        },
        {
            'name': 'James',
            'location': 'Embarcadero',
            'start': '10:30',
            'end': '11:30',
            'duration': 30
        },
        {
            'name': 'Linda',
            'location': 'Haight-Ashbury',
            'start': '7:30',
            'end': '19:15',
            'duration': 15
        },
        {
            'name': 'Paul',
            'location': "Fisherman's Wharf",
            'start': '14:45',
            'end': '18:45',
            'duration': 90
        },
        {
            'name': 'Anthony',
            'location': 'Mission District',
            'start': '8:00',
            'end': '14:45',
            'duration': 105
        },
        {
            'name': 'Nancy',
            'location': 'Alamo Square',
            'start': '8:30',
            'end': '13:45',
            'duration': 120
        },
        {
            'name': 'William',
            'location': 'Bayview',
            'start': '17:30',
            'end': '20:30',
            'duration': 120
        },
        {
            'name': 'Margaret',
            'location': 'Richmond District',
            'start': '15:15',
            'end': '18:15',
            'duration': 45
        }
    ]

    # Parse friends' data into minutes
    friends = []
    locations = [
        'Russian Hill',
        'Pacific Heights',
        'North Beach',
        'Golden Gate Park',
        'Embarcadero',
        'Haight-Ashbury',
        "Fisherman's Wharf",
        'Mission District',
        'Alamo Square',
        'Bayview',
        'Richmond District'
    ]

    for entry in friends_data:
        name = entry['name']
        location = entry['location']
        start_h, start_m = map(int, entry['start'].split(':'))
        start_time = start_h * 60 + start_m
        end_h, end_m = map(int, entry['end'].split(':'))
        end_time = end_h * 60 + end_m
        duration = entry['duration']
        friends.append({
            'name': name,
            'location': location,
            'start_time': start_time,
            'end_time': end_time,
            'required_duration': duration,
            'location_index': locations.index(location)
        })

    # Define travel times matrix
    travel_time = [
        # From Russian Hill (0)
        [0, 7, 5, 21, 8, 17, 7, 16, 15, 23, 14],
        # From Pacific Heights (1)
        [7, 0, 9, 15, 10, 11, 13, 15, 10, 22, 12],
        # From North Beach (2)
        [4, 8, 0, 22, 6, 18, 5, 18, 16, 25, 18],
        # From Golden Gate Park (3)
        [19, 16, 23, 0, 25, 7, 24, 17, 9, 23, 7],
        # From Embarcadero (4)
        [8, 11, 5, 25, 0, 21, 6, 20, 19, 21, 21],
        # From Haight-Ashbury (5)
        [17, 12, 19, 7, 20, 0, 23, 11, 5, 18, 10],
        # From Fisherman's Wharf (6)
        [7, 12, 6, 25, 8, 22, 0, 22, 21, 26, 18],
        # From Mission District (7)
        [15, 16, 17, 17, 19, 12, 22, 0, 11, 14, 20],
        # From Alamo Square (8)
        [13, 10, 15, 9, 16, 5, 19, 10, 0, 16, 11],
        # From Bayview (9)
        [23, 23, 22, 22, 19, 19, 25, 13, 16, 0, 27],
        # From Richmond District (10)
        [13, 10, 17, 9, 19, 10, 18, 20, 13, 27, 0]
    ]

    num_friends = len(friends)

    @lru_cache(maxsize=None)
    def dp(current_time, current_location, bitmask):
        max_count = 0
        for friend_idx in range(num_friends):
            if not (bitmask & (1 << friend_idx)):
                friend = friends[friend_idx]
                friend_loc = friend['location_index']
                travel_time_minutes = travel_time[current_location][friend_loc]
                arrival_time = current_time + travel_time_minutes
                required_duration = friend['required_duration']
                if arrival_time + required_duration > friend['end_time']:
                    continue
                meeting_start = max(arrival_time, friend['start_time'])
                meeting_end = meeting_start + required_duration
                if meeting_end > friend['end_time']:
                    continue
                new_bitmask = bitmask | (1 << friend_idx)
                count = 1 + dp(meeting_end, friend_loc, new_bitmask)
                if count > max_count:
                    max_count = count
        return max_count

    # Initial state: 9:00 AM (540 minutes), at Russian Hill (location 0), no friends met
    max_count = dp(540, 0, 0)

    # Reconstruct the path
    current_time = 540
    current_location = 0
    bitmask = 0
    path = []
    while True:
        best_count = dp(current_time, current_location, bitmask)
        if best_count == 0:
            break
        found = False
        for friend_idx in range(num_friends):
            if not (bitmask & (1 << friend_idx)):
                friend = friends[friend_idx]
                friend_loc = friend['location_index']
                travel_time_minutes = travel_time[current_location][friend_loc]
                arrival_time = current_time + travel_time_minutes
                required_duration = friend['required_duration']
                if arrival_time + required_duration > friend['end_time']:
                    continue
                meeting_start = max(arrival_time, friend['start_time'])
                meeting_end = meeting_start + required_duration
                if meeting_end > friend['end_time']:
                    continue
                new_bitmask = bitmask | (1 << friend_idx)
                new_count = 1 + dp(meeting_end, friend_loc, new_bitmask)
                if new_count == best_count:
                    path.append(friend_idx)
                    bitmask = new_bitmask
                    current_time = meeting_end
                    current_location = friend_loc
                    found = True
                    break
        if not found:
            break

    # Generate itinerary
    itinerary = []
    current_time = 540
    current_location = 0
    for friend_idx in path:
        friend = friends[friend_idx]
        friend_loc = friend['location_index']
        travel_time_minutes = travel_time[current_location][friend_loc]
        arrival_time = current_time + travel_time_minutes
        required_duration = friend['required_duration']
        meeting_start = max(arrival_time, friend['start_time'])
        meeting_end = meeting_start + required_duration
        start_h = meeting_start // 60
        start_m = meeting_start % 60
        end_h = meeting_end // 60
        end_m = meeting_end % 60
        start_str = f"{start_h}:{start_m:02d}"
        end_str = f"{end_h}:{end_m:02d}"
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_str,
            "end_time": end_str
        })
        current_time = meeting_end
        current_location = friend_loc

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()