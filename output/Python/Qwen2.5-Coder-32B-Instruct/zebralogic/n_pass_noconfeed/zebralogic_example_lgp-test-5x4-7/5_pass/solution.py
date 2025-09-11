# Define the number of houses
num_houses = 5  # Example number of houses

# Create a list representing the houses
houses = list(range(num_houses))

# Example mappings for animals and nationalities
# These should be defined according to your specific problem
animal_map = ['cat', 'dog', 'bird', 'fish', 'dog']  # Example animal map
nationality_map = ['german', 'spanish', 'brit', 'italian', 'french']  # Example nationality map

# Now you can use these in your condition
condition = any(animal_map[i] == 'dog' and nationality_map[i + 2] == 'brit' for i in range(len(houses) - 2))

print(condition)