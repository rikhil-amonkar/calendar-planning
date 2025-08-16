from itertools import permutations, combinations
from z3 import Solver, Int, sat, ModelRef

# Define travel times between locations
travel_times = {
    'Chinatown': {
        'Mission District': 18,
        'Alamo Square': 17,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Sunset District': 29,
        'Presidio': 19,
    },
    'Mission District': {
        'Chinatown': 16,
        'Alamo Square': 11,
        'Pacific Heights': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Sunset District': 24,
        'Presidio': 25,
    },
    'Alamo Square': {
        'Chinatown': 16,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Union Square': 14,
        'Golden Gate Park': 9,
        'Sunset District': 16,
        'Presidio': 18,
    },
    'Pacific Heights': {
        'Chinatown': 11,
        'Mission District': 15,
        'Alamo Square': 10,
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Sunset District': 21,
        'Presidio': 11,
    },
    'Union Square': {
        'Chinatown': 7,
        'Mission District': 14,
        'Alamo Square': 15,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'Sunset District': 26,
        'Presidio': 24,
    },
    'Golden Gate Park': {
        'Chinatown': 23,
        'Mission District': 17,
        'Alamo Square': 10,
        'Pacific Heights': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Presidio': 11,
    },
    'Sunset District': {
        'Chinatown': 30,
        'Mission District': 24,
        'Alamo Square': 17,
        'Pacific Heights': 21,
        'Union Square': 30,
        'Golden Gate Park': 11,
        'Presidio': 15,
    },
    'Presidio': {
        'Chinatown': 21,
        'Mission District': 26,
        'Alamo Square': 18,
        'Pacific Heights': 11,
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Sunset District': 15,
    }
}

# Define friends with their parameters
friends = [
    {
        'name': 'Deborah',
        'location': 'Golden Gate Park',
        'available_start': 7 * 60,  # 7:00 AM
        'available_end': 18 * 60 + 15,  # 6:15 PM
        'duration': 90
    },
    {
        'name': 'David',
        'location': 'Mission District',
        'available_start': 8 * 60,  # 8:00 AM
        'available_end': 19 * 60 + 45,  # 7:45 PM
        'duration': 45
    },
    {
        'name': 'Kenneth',
        'location': 'Alamo Square',
        'available_start': 14 * 60,  # 2:00 PM
        'available_end': 19 * 60 + 45,  # 7:45 PM
        'duration': 120
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': 17 * 60,  # 5:00 PM
        'available_end': 20 * 60,  # 8:00 PM
        'duration': 15
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'available_start': 17 * 60 + 45,  # 5:45 PM
        'available_end': 21 * 60 + 15,  # 9:15 PM
        'duration': 15
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'available_start': 21 * 60 + 45,  # 9:45 PM
        'available_end': 22 * 60 + 45,  # 10:45 PM
        'duration': 60
    }
]

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_optimal_schedule():
    for size in range(len(friends), 0, -1):
        for subset in combinations(friends, size):
            for perm in permutations(subset):
                solver = Solver()
                current_time = 9 * 60  # 9:00 AM
                previous_location = 'Chinatown'
                start_vars = {}
                for friend in perm:
                    location = friend['location']
                    travel_time = travel_times[previous_location][location]
                    arrival_time = current_time + travel_time
                    start = Int(f"{friend['name']}_start")
                    end = start + friend['duration']
                    # Add constraints
                    solver.add(start >= arrival_time)
                    solver.add(start >= friend['available_start'])
                    solver.add(end <= friend['available_end'])
                    start_vars[friend['name']] = start
                    current_time = end
                    previous_location = location
                if solver.check() == sat:
                    model = solver.model()
                    itinerary = []
                    for friend in perm:
                        start_time = model.evaluate(start_vars[friend['name']]).as_long()
                        end_time = start_time + friend['duration']
                        itinerary.append({
                            "action": "meet",
                            "person": friend['name'],
                            "start_time": minutes_to_time(start_time),
                            "end_time": minutes_to_time(end_time)
                        })
                    return {"itinerary": itinerary}
    return {"itinerary": []}  # No solution found

# Execute the function and print the result
solution = find_optimal_schedule()
print(solution)