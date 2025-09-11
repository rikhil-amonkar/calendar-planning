import permutations

# Define the constants
names = ['Alice', 'Bob', 'Eric', 'Peter', 'Clara']
foods = ['stew', 'grilled cheese', 'stir fry', 'pizza', 'spaghetti']
hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
heights = ['very tall', 'tall', 'average', 'short', 'very short']

# Clue 1: Bob's Hobby is Photography
# Clue 2: The painter is directly left of the grilled cheese (House 3)
# Clue 3: Peter is not in House 2
# Clue 4: The tall person (House 3) is directly left of stir fry (House 4)
# Clue 5: Cooking is done by the person with average height
# Clue 6: Alice is directly left of pizza
# Clue 7: Spaghetti is not in House 2
# Clue 8: Eric is not in House 5
# Clue 9: Peter is the short person
# Clue 10: Average height person is next to gardening
# Clue 11: The painter is directly left of grilled cheese (House 3)
# Clue 12: House 5 is very short
# Clue 13: House 3 is tall
# Clue 14: Alice is to the right of Bob (photography)

# Iterate over all permutations for each attribute
for name_perm in permutations(names):
    for food_perm in permutations(foods):
        for hobby_perm in permutations(hobbies):
            for height_perm in permutations(heights):
                # Assign each house's attributes
                houses = [
                    {'name': name_perm[0], 'food': food_perm[0], 'hobby': hobby_perm[0], 'height': height_perm[0]},
                    {'name': name_perm[1], 'food': food_perm[1], 'hobby': hobby_perm[1], 'height': height_perm[1]},
                    {'name': name_perm[2], 'food': food_perm[2], 'hobby': hobby_perm[2], 'height': height_perm[2]},
                    {'name': name_perm[3], 'food': food_perm[3], 'hobby': hobby_perm[3], 'height': height_perm[3]},
                    {'name': name_perm[4], 'food': food_perm[4], 'hobby': hobby_perm[4], 'height': height_perm[4]},
                ]

                # Apply the clues
                if (houses[2]['food'] != 'grilled cheese'): continue  # Clue 2
                if (houses[3]['food'] != 'stir fry'): continue  # Clue 4
                if (houses[