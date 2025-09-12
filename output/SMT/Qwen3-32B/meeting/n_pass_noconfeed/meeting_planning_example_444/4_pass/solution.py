# Define the dictionary with friend indices and their corresponding values
friend_values = {
    0: 10,
    1: 31,
    2: 7,
    3: 23,
    4: 23
}

# Iterate over the friend indices and retrieve their values
for friend_i in friend_values:
    value = friend_values.get(friend_i, 0)
    print(f"Friend {friend_i} has value: {value}")