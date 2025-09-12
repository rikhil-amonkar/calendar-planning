# Define travel times between locations
travel_times = {
    'Presidio': {
        'SFO': 15,
        'San Francisco': 10,
        'Oakland': 30
    },
    # Add more locations and travel times as needed
}

# Define list of friends with their locations
friends = [
    {'location': 'SFO'},
    {'location': 'San Francisco'},
    {'location': 'Oakland'}
]

# Loop over each friend to calculate travel time from Presidio
for fi in range(len(friends)):
    travel_time_0 = travel_times['Presidio'][friends[fi]['location']]
    print(f"Travel time to {friends[fi]['location']}: {travel_time_0} minutes")