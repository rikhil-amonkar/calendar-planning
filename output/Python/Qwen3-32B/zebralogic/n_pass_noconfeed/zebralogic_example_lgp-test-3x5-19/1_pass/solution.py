import itertools
import json

# Define the possible values for each category
names = ['Arnold', 'Peter', 'Eric']
occupations = ['doctor', 'teacher', 'engineer']
education = ['associate', 'high school', 'bachelor']
smoothies = ['desert', 'cherry', 'watermelon']
hobbies = ['gardening', 'cooking', 'photography']

solution_found = None

for name_perm in itertools.permutations(names):
    for occ_perm in itertools.permutations(occupations):
        for educ_perm in itertools.permutations(education):
            for smoothie_perm in itertools.permutations(smoothies):
                for hobby_perm in itertools.permutations(hobbies):
                    # Check clue 4: cooking in second house
                    if hobby_perm[1] != 'cooking':
                        continue
                    # Check clue 5: Peter in second house
                    if name_perm[1] != 'Peter':
                        continue
                    # Check clue 8: doctor in second house
                    if occ_perm[1] != 'doctor':
                        continue
                    # Check clue 1: desert smoothie in second house
                    if smoothie_perm[1] != 'desert':
                        continue
                    # Check clue 2: Arnold not in third house
                    if name_perm[2] == 'Arnold':
                        continue
                    # Check clue 3: cherry to the right of Peter (third house)
                    if smoothie_perm[2] != 'cherry':
                        continue
                    # Check clue 7: bachelor to the right of desert (third house)
                    if educ_perm[2] != 'bachelor':
                        continue
                    # Check clue 6: associate is to the right of gardening
                    gardening_index = hobby_perm.index('gardening')
                    associate_index = educ_perm.index('associate')
                    if associate_index <= gardening_index:
                        continue
                    # Check clue 9: teacher and photography in same house
                    teacher_index = occ_perm.index('teacher')
                    photo_index = hobby_perm.index('photography')
                    if teacher_index != photo_index:
                        continue
                    
                    # All constraints are satisfied
                    solution_found = []
                    for i in range(3):
                        house_num = str(i + 1)
                        name = name_perm[i]
                        occ = occ_perm[i]
                        educ = educ_perm[i]
                        smoothie = smoothie_perm[i]
                        hobby = hobby_perm[i]
                        solution_found.append([house_num, name, occ, educ, smoothie, hobby])
                    # Break out of loops once solution is found
                    break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Prepare the JSON output
json_output = {
    "solution": {
        "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
        "rows": solution_found
    }
}

# Print the JSON output
print(json.dumps(json_output))