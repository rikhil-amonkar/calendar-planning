# Define the dictionary with friend indices and their corresponding values
friend_values = {
    0: 10,
    1: 31,
    2: 7,
    3: 23,
    4: 23
}

# Dictionary to track which friends share the same value
value_to_friends = {}

# Group friends by their values
for friend, value in friend_values.items():
    if value not in value_to_friends:
        value_to_friends[value] = []
    value_to_friends[value].append(friend)

# Detect and report duplicates
duplicate_found = False
for value, friends in value_to_friends.items():
    if len(friends) > 1:
        print(f"Duplicate value {value} found among friends: {friends}")
        duplicate_found = True

if not duplicate_found:
    print("No duplicate values found. The data is unique.")
else:
    print("Duplicates detected. Consider adjusting the plan to avoid redundancy.")