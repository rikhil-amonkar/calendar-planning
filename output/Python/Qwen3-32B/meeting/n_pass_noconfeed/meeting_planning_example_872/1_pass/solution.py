import json
from functools import lru_cache

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define friends' constraints
    friends = [
        {
            'name': 'Karen',
            'location': 'Haight-Ashbury',
            'available_start': 21 * 60,  # 9:00 PM
            'available_end': 21 * 60 + 45,  # 9:45 PM
            'required_duration': 45
        },
        {
            'name': 'Jessica',
            'location': 'Nob Hill',
            'available_start': 13 * 60 + 45,  # 1:45 PM
            'available_end': 21 * 60,  # 9:00 PM
            'required_duration': 90
        },
        {
            'name': 'Brian',
            'location': 'Russian Hill',
            'available_start': 15 * 60 + 30,  # 3:30 PM
            'available_end': 21 * 60 + 45,  # 9:45 PM
            'required_duration': 60
        },
        {
            'name': 'Kenneth',
            'location': 'North Beach',
            'available_start': 9 * 60 + 45,  # 9:45 AM
            'available_end': 21 * 60,  # 9:00 PM
            'required_duration': 30
        },
        {
            'name': 'Jason',
            'location': 'Chinatown',
            'available_start': 8 * 60 + 15,  # 8:15 AM
            'available_end': 11 * 60 + 45,  # 11:45 AM
            'required_duration': 75
        },
        {
            'name': 'Stephanie',
            'location': 'Union Square',
            'available_start': 14 * 60 + 45,  # 2:45 PM
            'available_end': 18 * 60 + 45,  # 6:45 PM
            'required_duration': 105
        },
        {
            'name': 'Kimberly',
            'location': 'Embarcadero',
            'available_start': 9 * 60 + 45,  # 9:45 AM
            'available_end': 19 * 60 + 30,  # 7:30 PM
            'required_duration': 75
        },
        {
            'name': 'Steven',
            'location': 'Financial District',
            'available_start': 7 * 60 + 15,  # 7:15 AM
            'available_end': 21 * 60 + 15,  # 9:15 PM
            'required_duration': 60
        },
        {
            'name': 'Mark',
            'location': 'Marina District',
            'available_start': 10 * 60 + 15,  # 10:15 AM
            'available_end': 13 * 60,  # 1:00 PM
            'required_duration': 75
        }
    ]

    # Precompute location indices for each friend
    locations = [
        'Presidio',
        'Haight-Ashbury',
        'Nob Hill',
        'Russian Hill',
        'North Beach',
        'Chinatown',
        'Union Square',
        'Embarcadero',
        'Financial District',
        'Marina District'
    ]

    for friend in friends:
        friend['location_index'] = locations.index(friend['location'])

    # Define travel times between locations
    travel_times_data = [
        # Presidio to others
        ('Presidio', 'Haight-Ashbury', 15),
        ('Presidio', 'Nob Hill', 18),
        ('Presidio', 'Russian Hill', 14),
        ('Presidio', 'North Beach', 18),
        ('Presidio', 'Chinatown', 21),
        ('Presidio', 'Union Square', 22),
        ('Presidio', 'Embarcadero', 20),
        ('Presidio', 'Financial District', 23),
        ('Presidio', 'Marina District', 11),
        # Haight-Ashbury to others
        ('Haight-Ashbury', 'Presidio', 15),
        ('Haight-Ashbury', 'Nob Hill', 15),
        ('Haight-Ashbury', 'Russian Hill', 17),
        ('Haight-Ashbury', 'North Beach', 19),
        ('Haight-Ashbury', 'Chinatown', 19),
        ('Haight-Ashbury', 'Union Square', 19),
        ('Haight-Ashbury', 'Embarcadero', 20),
        ('Haight-Ashbury', 'Financial District', 21),
        ('Haight-Ashbury', 'Marina District', 17),
        # Nob Hill to others
        ('Nob Hill', 'Presidio', 17),
        ('Nob Hill', 'Haight-Ashbury', 13),
        ('Nob Hill', 'Russian Hill', 5),
        ('Nob Hill', 'North Beach', 8),
        ('Nob Hill', 'Chinatown', 6),
        ('Nob Hill', 'Union Square', 7),
        ('Nob Hill', 'Embarcadero', 9),
        ('Nob Hill', 'Financial District', 9),
        ('Nob Hill', 'Marina District', 11),
        # Russian Hill to others
        ('Russian Hill', 'Presidio', 14),
        ('Russian Hill', 'Haight-Ashbury', 17),
        ('Russian Hill', 'Nob Hill', 5),
        ('Russian Hill', 'North Beach', 5),
        ('Russian Hill', 'Chinatown', 9),
        ('Russian Hill', 'Union Square', 10),
        ('Russian Hill', 'Embarcadero', 8),
        ('Russian Hill', 'Financial District', 11),
        ('Russian Hill', 'Marina District', 7),
        # North Beach to others
        ('North Beach', 'Presidio', 17),
        ('North Beach', 'Haight-Ashbury', 18),
        ('North Beach', 'Nob Hill', 7),
        ('North Beach', 'Russian Hill', 4),
        ('North Beach', 'Chinatown', 6),
        ('North Beach', 'Union Square', 7),
        ('North Beach', 'Embarcadero', 6),
        ('North Beach', 'Financial District', 8),
        ('North Beach', 'Marina District', 9),
        # Chinatown to others
        ('Chinatown', 'Presidio', 19),
        ('Chinatown', 'Haight-Ashbury', 19),
        ('Chinatown', 'Nob Hill', 9),
        ('Chinatown', 'Russian Hill', 7),
        ('Chinatown', 'North Beach', 3),
        ('Chinatown', 'Union Square', 7),
        ('Chinatown', 'Embarcadero', 5),
        ('Chinatown', 'Financial District', 5),
        ('Chinatown', 'Marina District', 12),
        # Union Square to others
        ('Union Square', 'Presidio', 24),
        ('Union Square', 'Haight-Ashbury', 18),
        ('Union Square', 'Nob Hill', 9),
        ('Union Square', 'Russian Hill', 13),
        ('Union Square', 'North Beach', 10),
        ('Union Square', 'Chinatown', 7),
        ('Union Square', 'Embarcadero', 11),
        ('Union Square', 'Financial District', 9),
        ('Union Square', 'Marina District', 18),
        # Embarcadero to others
        ('Embarcadero', 'Presidio', 20),
        ('Embarcadero', 'Haight-Ashbury', 21),
        ('Embarcadero', 'Nob Hill', 10),
        ('Embarcadero', 'Russian Hill', 8),
        ('Embarcadero', 'North Beach', 5),
        ('Embarcadero', 'Chinatown', 7),
        ('Embarcadero', 'Union Square', 10),
        ('Embarcadero', 'Financial District', 5),
        ('Embarcadero', 'Marina District', 12),
        # Financial District to others
        ('Financial District', 'Presidio', 22),
        ('Financial District', 'Haight-Ashbury', 19),
        ('Financial District', 'Nob Hill', 8),
        ('Financial District', 'Russian Hill', 11),
        ('Financial District', 'North Beach', 7),
        ('Financial District', 'Chinatown', 5),
        ('Financial District', 'Union Square', 9),
        ('Financial District', 'Embarcadero', 4),
        ('Financial District', 'Marina District', 15),
        # Marina District to others
        ('Marina District', 'Presidio', 10),
        ('Marina District', 'Haight-Ashbury', 16),
        ('Marina District', 'Nob Hill', 12),
        ('Marina District', 'Russian Hill', 8),
        ('Marina District', 'North Beach', 11),
        ('Marina District', 'Chinatown', 15),
        ('Marina District', 'Union Square', 16),
        ('Marina District', 'Embarcadero', 14),
        ('Marina District', 'Financial District', 17),
    ]

    # Initialize travel_time matrix
    travel_time = [[0 for _ in range(len(locations))] for _ in range(len(locations))]
    for from_loc, to_loc, time in travel_times_data:
        from_index = locations.index(from_loc)
        to_index = locations.index(to_loc)
        travel_time[from_index][to_index] = time

    num_friends = len(friends)

    @lru_cache(maxsize=None)
    def dp(current_time, current_location_index, mask):
        max_count = 0
        best_path = []

        for friend_index in range(num_friends):
            if not (mask & (1 << friend_index)):
                # Friend not visited yet
                friend = friends[friend_index]
                friend_loc_index = friend['location_index']

                # Calculate arrival time at friend's location
                travel_time_minutes = travel_time[current_location_index][friend_loc_index]
                arrival_time = current_time + travel_time_minutes

                # Check if arrival_time is within friend's available time
                if arrival_time > friend['available_end']:
                    continue  # Can't meet this friend
                # Check if the meeting can be scheduled
                meeting_end_time = arrival_time + friend['required_duration']
                if meeting_end_time > friend['available_end']:
                    continue  # Not enough time for the meeting

                # This friend can be met. Now, compute the new state
                new_mask = mask | (1 << friend_index)
                new_time = meeting_end_time
                new_location_index = friend_loc_index

                # Recursively call dp for the new state
                next_count, next_path = dp(new_time, new_location_index, new_mask)

                total_count = 1 + next_count

                if total_count > max_count:
                    max_count = total_count
                    best_path = [friend_index] + next_path

        return (max_count, best_path)

    # Initial call: current_time is 9:00 AM (540), current_location_index is 0 (Presidio), mask is 0
    max_count, best_path_indices = dp(540, 0, 0)

    # Now, convert best_path_indices to the actual itinerary
    itinerary = []
    current_time = 540
    current_location_index = 0

    for friend_index in best_path_indices:
        friend = friends[friend_index]
        friend_loc_index = friend['location_index']

        # Calculate arrival time
        travel_time_minutes = travel_time[current_location_index][friend_loc_index]
        arrival_time = current_time + travel_time_minutes

        # Meeting starts at arrival_time, ends at arrival_time + duration
        meeting_duration = friend['required_duration']
        meeting_end_time = arrival_time + meeting_duration

        # Convert times to H:MM format
        start_time = time_to_str(arrival_time)
        end_time = time_to_str(meeting_end_time)

        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_time,
            "end_time": end_time
        })

        # Update current_time and current_location_index
        current_time = meeting_end_time
        current_location_index = friend_loc_index

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()