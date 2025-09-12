# Define travel times between locations
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

# Initialize travel times with example data
travel_times = {
    ('Russian Hill', 'Pacific Heights'): 15,
    ('Pacific Heights', 'Russian Hill'): 15,
    ('North Beach', "Fisherman's Wharf"): 10,
    ("Fisherman's Wharf", 'North Beach'): 10,
    ('Golden Gate Park', 'Alamo Square'): 20,
    ('Alamo Square', 'Golden Gate Park'): 20,
    
    # Additional travel times to connect all locations in a path
    ('Pacific Heights', 'North Beach'): 25,
    ('North Beach', 'Pacific Heights'): 25,
    ("Fisherman's Wharf", 'Golden Gate Park'): 30,
    ('Golden Gate Park', "Fisherman's Wharf"): 30,
    ('Alamo Square', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Alamo Square'): 15,
    ('Haight-Ashbury', 'Richmond District'): 20,
    ('Richmond District', 'Haight-Ashbury'): 20,
    ('Richmond District', 'Bayview'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 18,
    ('Mission District', 'Bayview'): 18,
    ('Mission District', 'Embarcadero'): 12,
    ('Embarcadero', 'Mission District'): 12,
}

# Add same-location travel times (time = 0)
for loc in locations:
    travel_times[(loc, loc)] = 0

def generate_route(locations, travel_times):
    current = locations[0]
    route = [current]
    visited = set([current])
    
    while len(route) < len(locations):
        min_time = float('inf')
        next_loc = None
        for loc in locations:
            if loc not in visited and (current, loc) in travel_times:
                if travel_times[(current, loc)] < min_time:
                    min_time = travel_times[(current, loc)]
                    next_loc = loc
        if next_loc is None:
            return None  # No valid route
        route.append(next_loc)
        visited.add(next_loc)
        current = next_loc
    return route

# Generate the route
route = generate_route(locations, travel_times)

# Calculate total travel time for the route
total_time = 0
for i in range(len(route) - 1):
    start = route[i]
    end = route[i + 1]
    total_time += travel_times[(start, end)]

# Output the plan
print("Valid Travel Plan:")
for loc in route:
    print(f" - {loc}")
print(f"\nTotal Travel Time: {total_time} minutes")