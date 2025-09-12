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
    ('North Beach', 'Fisherman\'s Wharf'): 10,
    ('Fisherman\'s Wharf', 'North Beach'): 10,
    ('Golden Gate Park', 'Alamo Square'): 20,
    ('Alamo Square', 'Golden Gate Park'): 20,
    # Add more travel times as needed
}

# Add same-location travel times (time = 0)
for loc in locations:
    travel_times[(loc, loc)] = 0

# Example usage
print(travel_times[('Russian Hill', 'Russian Hill')])  # Should print 0
print(travel_times[('Russian Hill', 'Pacific Heights')])  # Should print 15