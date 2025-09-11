# Example definitions (adjust based on your actual data)
food_perm = ['pizza', 'sushi', 'pasta', 'pizza']  # List of foods in permutation
peter_pos = 1  # Peter's position index (0-based)

# Check if the next person's food is not 'pizza'
if peter_pos + 1 < len(food_perm) and food_perm[peter_pos + 1] != 'pizza':
    # Add your intended code here, e.g., print a message or perform an action
    print("Next person is not having pizza.")
else:
    print("Next person is having pizza or out of bounds.")