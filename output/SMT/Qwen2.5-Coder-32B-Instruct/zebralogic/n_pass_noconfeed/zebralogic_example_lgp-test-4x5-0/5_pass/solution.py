from itertools import permutations

# Define the variables
names = ['Eric', 'Peter', 'Arnold', 'Alice']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
heights = ['tall', 'average', 'short', 'very short']
phone_models = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

houses = [1, 2, 3, 4]

# Function to check if the assignment satisfies all constraints
def check_constraints(name_assignment, smoothie_assignment, cigar_assignment, height_assignment, phone_model_assignment):
    # Clue 1: The Dragonfruit smoothie lover is Eric.
    if smoothie_assignment[names.index('Eric')] != smoothies.index('dragonfruit'):
        return False
    
    # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
    if cigar_assignment[smoothie_assignment.index(smoothies.index('cherry'))] != cigars.index('dunhill'):
        return False
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    if phone_model_assignment.index(phone_models.index('samsung galaxy s21')) + 1 != phone_model_assignment.index(phone_models.index('iphone 13')):
        return False
    
    # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
    if cigar_assignment[phone_model_assignment.index(phone_models.index('oneplus 9'))] != cigars.index('prince'):
        return False
    
    # Clue 7: The person who is tall is in the third house.
    if height_assignment[2] != heights.index('tall'):
        return False
    
    # Clue 8: The person who is very short is the person who uses an iPhone 13.
    if height_assignment[phone_model_assignment.index(phone_models.index('iphone 13'))] != heights.index('very short'):
        return False
    
    # Clue 9: The person who smokes Blue Master is not in the first house.
    if cigar_assignment[0] == cigars.index('blue master'):
        return False
    
    # Clue 10: The Dunhill smoker is the person who is short.
    if cigar_assignment[height_assignment.index(heights.index('short'))] != cigars.index('dunhill'):
        return False
    
    # Clue 11: Peter is not in the third house.
    if name_assignment[2] == names.index('Peter'):
        return False
    
    # Clue 12: Arnold is the person who uses a Google Pixel 6.
    if phone_model_assignment[name_assignment.index(names.index('Arnold'))] != phone_models.index('google pixel 6'):
        return False
    
    # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
    if cigar_assignment[smoothie_assignment.index(smoothies.index('dragonfruit'))] != cigars.index('pall mall'):
        return False
    
    return True

# Generate all possible permutations for assignments
for name_perm in permutations(range(len(names))):
    for smoothie_perm in permutations(range(len(smoothies))):
        for cigar_perm in permutations(range(len(cigars))):
            for height_perm in permutations(range(len(heights))):
                for phone_model_perm in permutations(range(len(phone_models))):
                    if check_constraints(name_perm, smoothie_perm, cigar_perm, height_perm, phone_model_perm):
                        solution = []
                        for house in houses:
                            name = names[name_perm[house - 1]]
                            smoothie = smoothies[smoothie_perm[house - 1]]
                            cigar = cigars[cigar_perm[house - 1]]
                            height = heights[height_perm[house - 1]]
                            phone_model = phone_models[phone_model_perm[house - 1]]
                            solution.append([str(house), name, smoothie, cigar, height, phone_model])
                        import json
                        print(json.dumps({
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                                "rows": solution
                            }
                        }))
                        break
                else:
                    continue
                break
            else:
                continue
            break
        else:
            continue
        break
else:
    print("No solution found")