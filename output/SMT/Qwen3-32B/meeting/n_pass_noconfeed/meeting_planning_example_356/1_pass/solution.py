import z3
import itertools
import json

# Travel times between locations in minutes
travel_times = {
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Union Square'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
}

# Friend meeting constraints (converted to minutes since midnight)
friends = [
    {
        'name': 'Barbara',
        'location': 'North Beach',
        'start': 825,  # 1:45 PM
        'end': 1215,   # 8:15 PM
        'duration': 60
    },
    {
        'name': 'Margaret',
        'location': 'Presidio',
        'start': 615,  # 10:15 AM
        'end': 915,    # 3:15 PM
        'duration': 30
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'start': 1200, # 8:00 PM
        'end': 1245,   # 8:45 PM
        'duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Union Square',
        'start': 465,  # 7:45 AM
        'end': 1005,   # 4:45 PM
        'duration': 30
    }
]

# Try to find the optimal meeting schedule
for subset_size in range(4, 0, -1):
    for perm in itertools.permutations(friends, subset_size):
        solver = z3.Solver()
        arrival_times = [z3.Int(f'arrival_{i}') for i in range(subset_size)]
        prev_departure = 540  # Start at Bayview at 9:00 AM (540 minutes)
        prev_location = 'Bayview'
        for i in range(subset_size):
            friend = perm[i]
            current_location = friend['location']
            travel_time = travel_times[(prev_location, current_location)]
            # Arrival time must be >= previous departure + travel time
            solver.add(arrival_times[i] >= prev_departure + travel_time)
            # Meeting must end before the friend's end time
            solver.add(arrival_times[i] + friend['duration'] <= friend['end'])
            # Update previous departure and location
            prev_departure = arrival_times[i] + friend['duration']
            prev_location = current_location
        if solver.check() == z3.sat:
            model = solver.model()
            itinerary = []
            for i in range(subset_size):
                friend = perm[i]
                arrival = model[arrival_times[i]].as_long()
                end_time = arrival + friend['duration']
                # Convert to 24-hour format
                start_h, start_m = divmod(arrival, 60)
                end_h, end_m = divmod(end_time, 60)
                # Format as H:MM without leading zero
                start_str = f"{start_h}:{start_m:02d}"
                end_str = f"{end_h}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
            print(json.dumps({"itinerary": itinerary}, indent=2))
            exit()

print(json.dumps({"itinerary": []}))