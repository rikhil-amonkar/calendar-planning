# Define friends with their locations
friends = [
    {'location': 'Home'},
    {'location': 'Office'},
    {'location': 'Library'},
    {'location': 'Park'},
    {'location': 'Mall'}
]

# Define travel times between different locations
travel_times = {
    ('Home', 'Office'): 20,
    ('Home', 'Library'): 15,
    ('Home', 'Park'): 10,
    ('Home', 'Mall'): 12,
    ('Office', 'Library'): 25,
    ('Office', 'Park'): 30,
    ('Office', 'Mall'): 18,
    ('Library', 'Park'): 22,
    ('Library', 'Mall'): 10,
    ('Park', 'Mall'): 15
}

# Initialize travel_times_between_friends as a 5x5 matrix
travel_times_between_friends = [[0 for _ in range(5)] for _ in range(5)]

# Calculate travel times between friends based on their locations
for prev in range(5):
    for curr in range(5):
        prev_loc = friends[prev]['location']
        curr_loc = friends[curr]['location']
        if prev_loc == curr_loc:
            travel_times_between_friends[prev][curr] = 0
        else:
            travel_times_between_friends[prev][curr] = travel_times[(prev_loc, curr_loc)]