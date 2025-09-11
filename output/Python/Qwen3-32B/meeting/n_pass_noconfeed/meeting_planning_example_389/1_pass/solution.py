import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Define friends' data
friends = [
    {
        'name': 'Sarah',
        'location': "Fisherman's Wharf",
        'available_start': time_str_to_minutes("14:45"),
        'available_end': time_str_to_minutes("17:30"),
        'required_duration': 105
    },
    {
        'name': 'Mary',
        'location': 'Richmond District',
        'available_start': time_str_to_minutes("13:00"),
        'available_end': time_str_to_minutes("19:15"),
        'required_duration': 75
    },
    {
        'name': 'Helen',
        'location': 'Mission District',
        'available_start': time_str_to_minutes("21:45"),
        'available_end': time_str_to_minutes("22:30"),
        'required_duration': 30
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': time_str_to_minutes("15:15"),
        'available_end': time_str_to_minutes("18:45"),
        'required_duration': 120
    }
]

# Define travel times
travel_times = {
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Richmond District'): 18,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13,
}

best_itinerary = []
max_met = 0

# Generate all permutations of friends
for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Haight-Ashbury'
    itinerary = []
    met_count = 0

    for friend in perm:
        # Calculate travel time
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            break
        current_time += travel_time

        # Check if meeting is possible
        available_start = friend['available_start']
        available_end = friend['available_end']
        required = friend['required_duration']

        earliest_start = max(current_time, available_start)
        latest_start = available_end - required

        if earliest_start > latest_start:
            break

        # Schedule the meeting
        meeting_start = earliest_start
        meeting_end = meeting_start + required

        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(meeting_start),
            'end_time': minutes_to_time_str(meeting_end)
        })
        met_count += 1

        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']

    # After processing all friends in permutation
    if met_count > max_met:
        max_met = met_count
        best_itinerary = itinerary

# Output the best itinerary as JSON
print(json.dumps({"itinerary": best_itinerary}))