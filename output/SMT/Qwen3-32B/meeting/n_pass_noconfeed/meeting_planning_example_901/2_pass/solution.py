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

travel_times = {
    # Existing travel times (as before) ...
}

# Add same-location travel times
for loc in locations:
    travel_times[(loc, loc)] = 0