# Define the friends with their locations
friends = [
    {'location': 'Home'},
    {'location': 'Office'},
    {'location': 'Cafe'},
    {'location': 'Park'},
    {'location': 'Gym'},
    {'location': 'Library'},
    {'location': 'Mall'}
]

# Define travel times between locations
travel_time_dict = {
    ('Home', 'Office'): 10,
    ('Office', 'Home'): 10,
    ('Home', 'Cafe'): 5,
    ('Cafe', 'Home'): 5,
    ('Home', 'Park'): 15,
    ('Park', 'Home'): 15,
    ('Home', 'Gym'): 20,
    ('Gym', 'Home'): 20,
    ('Home', 'Library'): 12,
    ('Library', 'Home'): 12,
    ('Home', 'Mall'): 8,
    ('Mall', 'Home'): 8,
    ('Office', 'Cafe'): 10,
    ('Cafe', 'Office'): 10,
    ('Office', 'Park'): 18,
    ('Park', 'Office'): 18,
    ('Office', 'Gym'): 22,
    ('Gym', 'Office'): 22,
    ('Office', 'Library'): 14,
    ('Library', 'Office'): 14,
    ('Office', 'Mall'): 16,
    ('Mall', 'Office'): 16,
    ('Cafe', 'Park'): 7,
    ('Park', 'Cafe'): 7,
    ('Cafe', 'Gym'): 10,
    ('Gym', 'Cafe'): 10,
    ('Cafe', 'Library'): 8,
    ('Library', 'Cafe'): 8,
    ('Cafe', 'Mall'): 6,
    ('Mall', 'Cafe'): 6,
    ('Park', 'Gym'): 12,
    ('Gym', 'Park'): 12,
    ('Park', 'Library'): 9,
    ('Library', 'Park'): 9,
    ('Park', 'Mall'): 11,
    ('Mall', 'Park'): 11,
    ('Gym', 'Library'): 13,
    ('Library', 'Gym'): 13,
    ('Gym', 'Mall'): 14,
    ('Mall', 'Gym'): 14,
    ('Library', 'Mall'): 10,
    ('Mall', 'Library'): 10
}

# Extract locations from friends
friend_locations = [friend['location'] for friend in friends]

# Initialize travel_time_between_friends as a 7x7 matrix
travel_time_between_friends = [[0 for _ in range(7)] for _ in range(7)]

# Calculate travel times between friends
for i in range(7):
    for j in range(7):
        from_loc = friend_locations[i]
        to_loc = friend_locations[j]
        if from_loc == to_loc:
            travel_time_between_friends[i][j] = 0
        else:
            travel_time_between_friends[i][j] = travel_time_dict[(from_loc, to_loc)]

# Output the result (for testing)
print(travel_time_between_friends)