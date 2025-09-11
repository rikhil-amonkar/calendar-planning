import json

def main():
    friends = [
        {
            'name': 'Helen',
            'location': 'Golden Gate Park',
            'available_start': 570,  # 9:30 AM
            'available_end': 735,    # 12:15 PM
            'required_duration': 45
        },
        {
            'name': 'Steven',
            'location': 'The Castro',
            'available_start': 1215,  # 8:15 PM
            'available_end': 1320,    # 10:00 PM
            'required_duration': 105
        },
        {
            'name': 'Deborah',
            'location': 'Bayview',
            'available_start': 510,   # 8:30 AM
            'available_end': 720,     # 12:00 PM
            'required_duration': 30
        },
        {
            'name': 'Matthew',
            'location': 'Marina District',
            'available_start': 555,   # 9:15 AM
            'available_end': 855,     # 2:15 PM
            'required_duration': 45
        },
        {
            'name': 'Joseph',
            'location': 'Union Square',
            'available_start': 855,   # 2:15 PM
            'available_end': 1125,    # 6:45 PM
            'required_duration': 120
        },
        {
            'name': 'Ronald',
            'location': 'Sunset District',
            'available_start': 960,   # 4:00 PM
            'available_end': 1245,    # 8:45 PM
            'required_duration': 60
        },
        {
            'name': 'Robert',
            'location': 'Alamo Square',
            'available_start': 1110,  # 6:30 PM
            'available_end': 1275,    # 9:15 PM
            'required_duration': 120
        },
        {
            'name': 'Rebecca',
            'location': 'Financial District',
            'available_start': 885,   # 2:45 PM
            'available_end': 975,     # 4:15 PM
            'required_duration': 30
        },
        {
            'name': 'Elizabeth',
            'location': 'Mission District',
            'available_start': 1110,  # 6:30 PM
            'available_end': 1260,    # 9:00 PM
            'required_duration': 120
        }
    ]

    locations = [
        'Pacific Heights',
        'Golden Gate Park',
        'The Castro',
        'Bayview',
        'Marina District',
        'Union Square',
        'Sunset District',
        'Alamo Square',
        'Financial District',
        'Mission District'
    ]

    travel_times = [
        # From Pacific Heights (0)
        [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],
        # From Golden Gate Park (1)
        [16, 0, 13, 23, 18, 22, 10, 9, 26, 17],
        # From The Castro (2)
        [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],
        # From Bayview (3)
        [23, 22, 19, 0, 27, 18, 23, 16, 19, 13],
        # From Marina District (4)
        [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],
        # From Union Square (5)
        [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],
        # From Sunset District (6)
        [21, 11, 17, 22, 21, 30, 0, 17, 30, 25],
        # From Alamo Square (7)
        [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],
        # From Financial District (8)
        [13, 23, 20, 19, 15, 9, 30, 17, 0, 15],
        # From Mission District (9)
        [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]
    ]

    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    def find_best_itinerary(current_time, current_location_index, visited):
        best_itinerary = []
        max_count = 0

        for friend_idx in range(len(friends)):
            if friend_idx in visited:
                continue

            friend = friends[friend_idx]
            friend_location_idx = locations.index(friend['location'])
            travel_time = travel_times[current_location_index][friend_location_idx]

            arrival_time = current_time + travel_time

            available_start = friend['available_start']
            available_end = friend['available_end']
            required_duration = friend['required_duration']

            start_time = max(arrival_time, available_start)
            end_time = start_time + required_duration

            if end_time > available_end:
                continue  # Can't meet this friend

            new_visited = visited.copy()
            new_visited.add(friend_idx)

            sub_itinerary = find_best_itinerary(end_time, friend_location_idx, new_visited)

            current_meeting = {
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': format_time(start_time),
                'end_time': format_time(end_time)
            }

            full_itinerary = [current_meeting] + sub_itinerary

            if len(full_itinerary) > max_count:
                max_count = len(full_itinerary)
                best_itinerary = full_itinerary

        return best_itinerary

    itinerary = find_best_itinerary(540, 0, set())

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()