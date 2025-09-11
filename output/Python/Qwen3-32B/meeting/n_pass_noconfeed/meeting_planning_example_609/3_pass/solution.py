import heapq
import json

def main():
    # Define travel times as a dictionary
    travel_times = {
        # All pairs as per input
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Presidio'): 19,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Presidio'): 25,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Presidio'): 18,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Presidio'): 11,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Presidio'): 24,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Presidio'): 16,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Sunset District'): 15,
    }

    # Define friends with their constraints
    friends = [
        {
            'name': 'David',
            'location': 'Mission District',
            'available_start': 480,  # 8:00 AM
            'available_end': 1185,   # 7:45 PM
            'duration': 45,
            'index': 0
        },
        {
            'name': 'Kenneth',
            'location': 'Alamo Square',
            'available_start': 840,  # 2:00 PM
            'available_end': 1185,   # 7:45 PM
            'duration': 120,
            'index': 1
        },
        {
            'name': 'John',
            'location': 'Pacific Heights',
            'available_start': 1020,  # 5:00 PM
            'available_end': 1200,    # 8:00 PM
            'duration': 15,
            'index': 2
        },
        {
            'name': 'Charles',
            'location': 'Union Square',
            'available_start': 1305,  # 9:45 PM
            'available_end': 1365,    # 10:45 PM
            'duration': 60,
            'index': 3
        },
        {
            'name': 'Deborah',
            'location': 'Golden Gate Park',
            'available_start': 420,   # 7:00 AM
            'available_end': 1095,    # 6:15 PM
            'duration': 90,
            'index': 4
        },
        {
            'name': 'Karen',
            'location': 'Sunset District',
            'available_start': 1065,  # 5:45 PM
            'available_end': 1275,    # 9:15 PM
            'duration': 15,
            'index': 5
        },
        {
            'name': 'Carol',
            'location': 'Presidio',
            'available_start': 495,   # 8:15 AM
            'available_end': 555,     # 9:15 AM
            'duration': 30,
            'index': 6
        }
    ]

    # Starting time and location
    start_time_minutes = 9 * 60  # 9:00 AM
    start_location = 'Chinatown'

    # Initialize priority queue
    heap = []
    initial_bitmask = 0
    initial_path = []
    # Priority is (-num_friends, current_time)
    heapq.heappush(heap, (0, start_time_minutes, start_location, initial_bitmask, initial_path))

    best_path = None

    while heap:
        priority, current_time, current_location, bitmask, path = heapq.heappop(heap)
        num_friends = -priority

        # Update best_path if this path is better
        if best_path is None or len(path) > len(best_path):
            best_path = path

        # Generate next states for each friend not yet met
        for friend in friends:
            if not (bitmask & (1 << friend['index'])):  # Friend not met
                from_loc = current_location
                to_loc = friend['location']
                travel_time = travel_times.get((from_loc, to_loc))
                if travel_time is None:
                    continue  # Should not happen with given input

                arrival_time = current_time + travel_time
                available_start = friend['available_start']
                available_end = friend['available_end']
                required = friend['duration']

                earliest_start = max(arrival_time, available_start)
                if earliest_start + required <= available_end:
                    new_time = earliest_start + required
                    new_location = to_loc
                    new_bitmask = bitmask | (1 << friend['index'])

                    # Create new meeting entry
                    start_hour = earliest_start // 60
                    start_min = earliest_start % 60
                    end_hour = (earliest_start + required) // 60
                    end_min = (earliest_start + required) % 60
                    start_time_str = f"{start_hour}:{start_min:02d}"
                    end_time_str = f"{end_hour}:{end_min:02d}"
                    meeting = {
                        'action': 'meet',
                        'location': to_loc,
                        'person': friend['name'],
                        'start_time': start_time_str,
                        'end_time': end_time_str
                    }
                    new_path = path + [meeting]

                    # Push to heap
                    heapq.heappush(heap, (
                        - (num_friends + 1),
                        new_time,
                        new_location,
                        new_bitmask,
                        new_path
                    ))

    # Output the best path as JSON
    result = {
        "itinerary": best_path
    }

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()