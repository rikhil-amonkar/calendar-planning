import itertools
import json

# Define friends with their constraints
friends = [
    {'name': 'Sarah', 'location': 'North Beach', 'available_start': 960, 'available_end': 1095, 'required': 60},
    {'name': 'Jeffrey', 'location': 'Union Square', 'available_start': 900, 'available_end': 1320, 'required': 75},
    {'name': 'Brian', 'location': 'Alamo Square', 'available_start': 960, 'available_end': 1050, 'required': 75},
]

# Define travel times between locations
travel_time = {
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14,
}

best_itinerary = []
best_num_friends = 0
best_end_time = float('inf')

initial_time = 9 * 60  # 9:00 AM in minutes since midnight
initial_location = 'Sunset District'

for r in range(3, 0, -1):  # Check for 3, 2, 1 friends
    for perm in itertools.permutations(friends, r):
        current_time = initial_time
        current_location = initial_location
        itinerary = []
        valid = True
        for friend in perm:
            # Calculate travel time
            from_loc = current_location
            to_loc = friend['location']
            travel_duration = travel_time[(from_loc, to_loc)]
            arrival_time = current_time + travel_duration

            # Check if meeting is possible
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required']

            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - required

            if earliest_start > latest_start:
                valid = False
                break

            # Schedule meeting
            meeting_start = earliest_start
            meeting_end = meeting_start + required

            # Convert times to H:MM format
            start_time_str = f"{meeting_start//60}:{meeting_start%60:02d}"
            end_time_str = f"{meeting_end//60}:{meeting_end%60:02d}"

            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })

            # Update current time and location
            current_time = meeting_end
            current_location = friend['location']

        if valid:
            num_friends = len(itinerary)
            end_time = current_time
            # Check if this is better than current best
            if (num_friends > best_num_friends) or \
               (num_friends == best_num_friends and end_time < best_end_time):
                best_num_friends = num_friends
                best_itinerary = itinerary
                best_end_time = end_time

# Generate JSON output
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))