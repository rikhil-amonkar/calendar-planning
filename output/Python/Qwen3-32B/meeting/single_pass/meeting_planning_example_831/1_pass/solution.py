import json
from functools import lru_cache

def main():
    # Define locations
    locations = [
        'Presidio',
        "Fisherman's Wharf",
        'Alamo Square',
        'Financial District',
        'Union Square',
        'Sunset District',
        'Embarcadero',
        'Golden Gate Park',
        'Chinatown',
        'Richmond District'
    ]
    location_to_index = {loc: idx for idx, loc in enumerate(locations)}

    # Define friends
    friends = [
        {
            'name': 'Ronald',
            'location': 'Alamo Square',
            'available_start': 7 * 60 + 45,  # 7:45 AM
            'available_end': 14 * 60 + 45,    # 2:45 PM
            'required_duration': 120
        },
        {
            'name': 'Jeffrey',
            'location': "Fisherman's Wharf",
            'available_start': 10 * 60 + 15,  # 10:15 AM
            'available_end': 13 * 60 + 0,     # 1:00 PM
            'required_duration': 90
        },
        {
            'name': 'Jason',
            'location': 'Financial District',
            'available_start': 10 * 60 + 45,  # 10:45 AM
            'available_end': 16 * 60 + 0,     # 4:00 PM
            'required_duration': 105
        },
        {
            'name': 'Melissa',
            'location': 'Union Square',
            'available_start': 17 * 60 + 45,  # 5:45 PM
            'available_end': 18 * 60 + 15,    # 6:15 PM
            'required_duration': 15
        },
        {
            'name': 'Elizabeth',
            'location': 'Sunset District',
            'available_start': 14 * 60 + 45,  # 2:45 PM
            'available_end': 17 * 60 + 30,    # 5:30 PM
            'required_duration': 105
        },
        {
            'name': 'Margaret',
            'location': 'Embarcadero',
            'available_start': 13 * 60 + 15,  # 1:15 PM
            'available_end': 19 * 60 + 0,     # 7:00 PM
            'required_duration': 90
        },
        {
            'name': 'George',
            'location': 'Golden Gate Park',
            'available_start': 19 * 60 + 0,   # 7:00 PM
            'available_end': 22 * 60 + 0,     # 10:00 PM
            'required_duration': 75
        },
        {
            'name': 'Richard',
            'location': 'Chinatown',
            'available_start': 9 * 60 + 30,   # 9:30 AM
            'available_end': 21 * 60 + 0,     # 9:00 PM
            'required_duration': 15
        },
        {
            'name': 'Laura',
            'location': 'Richmond District',
            'available_start': 9 * 60 + 45,   # 9:45 AM
            'available_end': 18 * 60 + 0,     # 6:00 PM
            'required_duration': 60
        }
    ]

    # Convert friend locations to indexes
    for friend in friends:
        friend['location_idx'] = location_to_index[friend['location']]

    # Define travel times between locations
    travel_times = {
        # Presidio to others
        ('Presidio', "Fisherman's Wharf"): 19,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Richmond District'): 7,
        # Fisherman's Wharf to others
        ("Fisherman's Wharf", 'Presidio'): 17,
        ("Fisherman's Wharf", 'Alamo Square'): 21,
        ("Fisherman's Wharf", 'Financial District'): 11,
        ("Fisherman's Wharf", 'Union Square'): 13,
        ("Fisherman's Wharf", 'Sunset District'): 27,
        ("Fisherman's Wharf", 'Embarcadero'): 8,
        ("Fisherman's Wharf", 'Golden Gate Park'): 25,
        ("Fisherman's Wharf", 'Chinatown'): 12,
        ("Fisherman's Wharf", 'Richmond District'): 18,
        # Alamo Square to others
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', "Fisherman's Wharf"): 19,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Richmond District'): 11,
        # Financial District to others
        ('Financial District', 'Presidio'): 22,
        ('Financial District', "Fisherman's Wharf"): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Richmond District'): 21,
        # Union Square to others
        ('Union Square', 'Presidio'): 24,
        ('Union Square', "Fisherman's Wharf"): 15,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Richmond District'): 20,
        # Sunset District to others
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', "Fisherman's Wharf"): 29,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Richmond District'): 12,
        # Embarcadero to others
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', "Fisherman's Wharf"): 6,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Richmond District'): 21,
        # Golden Gate Park to others
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', "Fisherman's Wharf"): 24,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Richmond District'): 7,
        # Chinatown to others
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', "Fisherman's Wharf"): 8,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Richmond District'): 20,
        # Richmond District to others
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', "Fisherman's Wharf"): 18,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Chinatown'): 20,
    }

    # Convert travel times to use indexes
    travel_times_idx = {}
    for (from_loc, to_loc), time in travel_times.items():
        from_idx = location_to_index[from_loc]
        to_idx = location_to_index[to_loc]
        travel_times_idx[(from_idx, to_idx)] = time

    # Function to convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    @lru_cache(maxsize=None)
    def dfs(current_loc_idx, current_time, visited_mask):
        max_count = 0
        best_itinerary = []

        for i in range(len(friends)):
            if not (visited_mask & (1 << i)):
                friend = friends[i]
                friend_loc_idx = friend['location_idx']
                travel_time = travel_times_idx.get((current_loc_idx, friend_loc_idx), float('inf'))
                arrival_time = current_time + travel_time

                available_start = friend['available_start']
                available_end = friend['available_end']
                required_duration = friend['required_duration']
                latest_start = available_end - required_duration

                if latest_start < available_start:
                    continue

                start_time = max(arrival_time, available_start)
                if start_time > latest_start:
                    continue

                end_time = start_time + required_duration
                if end_time > available_end:
                    continue

                # Recurse
                next_count, next_itinerary = dfs(friend_loc_idx, end_time, visited_mask | (1 << i))

                total_count = 1 + next_count
                if total_count > max_count:
                    max_count = total_count
                    start_str = minutes_to_time(start_time)
                    end_str = minutes_to_time(end_time)
                    new_entry = {
                        "action": "meet",
                        "location": friend['location'],
                        "person": friend['name'],
                        "start_time": start_str,
                        "end_time": end_str
                    }
                    best_itinerary = [new_entry] + next_itinerary

        # If no friends can be visited
        return (max_count, best_itinerary)

    # Initial call: current_loc is Presidio (index 0), current_time is 540 (9:00 AM), visited_mask is 0
    max_count, best_itinerary = dfs(0, 540, 0)

    # Output as JSON
    result = {
        "itinerary": best_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()