import itertools
import json

# Define the possible values for each attribute
names = ['Arnold', 'Peter', 'Eric']
occupations = ['doctor', 'teacher', 'engineer']
educations = ['associate', 'high school', 'bachelor']
smoothies = ['desert', 'cherry', 'watermelon']
hobbies = ['gardening', 'cooking', 'photography']

# Generate all possible permutations for one house
attributes = [names, occupations, educations, smoothies, hobbies]
all_permutations = list(itertools.permutations(range(3)))

# Function to check if a permutation satisfies all the constraints
def is_valid_solution(solution):
    # Unpack the solution into separate lists
    house_names = [solution[i][0] for i in range(3)]
    house_occupations = [solution[i][1] for i in range(3)]
    house_educations = [solution[i][2] for i in range(3)]
    house_smoothies = [solution[i][3] for i in range(3)]
    house_hobbies = [solution[i][4] for i in range(3)]

    # Check each constraint
    # 1. The Desert smoothie lover is the person who is a doctor.
    if house_smoothies.index('desert') != house_occupations.index('doctor'):
        return False
    
    # 2. Arnold is not in the third house.
    if house_names[2] == 'Arnold':
        return False
    
    # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
    if house_smoothies.index('cherry') < house_names.index('Peter'):
        return False
    
    # 4. The person who loves cooking is in the second house.
    if house_hobbies[1] != 'cooking':
        return False
    
    # 5. The person who loves cooking is Peter.
    if house_hobbies.index('cooking') != house_names.index('Peter'):
        return False
    
    # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    if house_educations.index('associate') < house_hobbies.index('gardening'):
        return False
    
    # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    if house_educations.index('bachelor') < house_smoothies.index('desert'):
        return False
    
    # 8. The person who loves cooking is the person who is a doctor.
    if house_hobbies.index('cooking') != house_occupations.index('doctor'):
        return False
    
    # 9. The photography enthusiast is the person who is a teacher.
    if house_hobbies.index('photography') != house_occupations.index('teacher'):
        return False
    
    return True

# Generate all possible solutions (permutations of attributes)
possible_solutions = list(itertools.permutations(attributes[0]))
possible_solutions = [(name, occ, edu, smth, hobby) for name, occ, edu, smth, hobby in possible_solutions]

# Check all combinations of three houses
for house1 in possible_solutions:
    for house2 in possible_solutions:
        for house3 in possible_solutions:
            solution = [house1, house2, house3]
            if len(set([house[0] for house in solution])) == 3 and \
               len(set([house[1] for house in solution])) == 3 and \
               len(set([house[2] for house in solution])) == 3 and \
               len(set([house[3] for house in solution])) == 3 and \
               len(set([house[4] for house in solution])) == 3 and \
               is_valid_solution(solution):
                # Format the solution as JSON
                result = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                        "rows": [
                            ["1", solution[0][0], solution[0][1], solution[0][2], solution[0][3], solution[0][4]],
                            ["2", solution[1][0], solution[1][1], solution[1][2], solution[1][3], solution[1][4]],
                            ["3", solution[2][0], solution[2][1], solution[2][2], solution[2][3], solution[2][4]]
                        ]
                    }
                }
                print(json.dumps(result, indent=2))
                break