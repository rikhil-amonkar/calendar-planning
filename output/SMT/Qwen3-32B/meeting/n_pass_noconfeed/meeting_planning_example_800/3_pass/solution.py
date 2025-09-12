# Define friends' locations (example values)
friends_locations = ['Home', 'Office', 'School', 'Park', 'Mall',
                     'Library', 'Gym', 'Cafe', 'Stadium']

# Initialize a 9x9 travel time matrix
friend_travel_times = [[0 for _ in range(9)] for _ in range(9)]

# Example travel times between locations (you can expand this as needed)
travel_times = {
    ('Home', 'Office'): 15,
    ('Office', 'Home'): 15,
    ('School', 'Park'): 10,
    ('Park', 'School'): 10,
    ('Mall', 'Library'): 20,
    ('Library', 'Mall'): 20,
    ('Gym', 'Cafe'): 5,
    ('Cafe', 'Gym'): 5,
    ('Stadium', 'Home'): 30,
    ('Home', 'Stadium'): 30,
}

# Populate the friend_travel_times matrix
for i in range(9):
    for j in range(9):
        from_loc = friends_locations[i]
        to_loc = friends_locations[j]
        if from_loc == to_loc:
            friend_travel_times[i][j] = 0
        else:
            friend_travel_times[i][j] = travel_times.get((from_loc, to_loc), float('inf'))

# Optional: Print the result
for row in friend_travel_times:
    print(row)