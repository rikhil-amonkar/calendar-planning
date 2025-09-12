import itertools

# Define the variables
houses = [1, 2, 3]
names = ['Peter', 'Arnold', 'Eric']
occupations = ['doctor', 'teacher', 'engineer']
hobbies = ['cooking', 'photography', 'gardening']

# Map names, occupations, and hobbies to integers
name_map = {name: i for i, name in enumerate(names)}
occupation_map = {occupation: i for i, occupation in enumerate(occupations)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}

# Function to check if a given assignment satisfies all constraints
def check_constraints(name_assignment, occupation_assignment, hobby_assignment):
    # Clue 1: The person who is a doctor and Eric are next to each other.
    for house in houses[:-1]:
        if (occupation_assignment[house] == occupation_map['doctor'] and name_assignment[house + 1] == name_map['Eric']) or \
           (name_assignment[house] == name_map['Eric'] and occupation_assignment[house + 1] == occupation_map['doctor']):
            continue
        else:
            return False
    
    # Clue 2: The person who loves cooking is directly left of the person who is a teacher.
    for house in houses[:-1]:
        if (hobby_assignment[house] == hobby_map['cooking'] and occupation_assignment[house + 1] == occupation_map['teacher']):
            continue
        else:
            return False
    
    # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
    if (hobby_assignment[1] == hobby_map['gardening'] and occupation_assignment[2] == occupation_map['doctor']) or \
       (hobby_assignment[1] == hobby_map['gardening'] and occupation_assignment[3] == occupation_map['doctor']) or \
       (hobby_assignment[2] == hobby_map['gardening'] and occupation_assignment[3] == occupation_map['doctor']):
        pass
    else:
        return False
    
    # Clue 4: The photography enthusiast is the person who is a teacher.
    for house in houses:
        if hobby_assignment[house] == hobby_map['photography'] and occupation_assignment[house] == occupation_map['teacher']:
            continue
        else:
            return False
    
    # Clue 5: The person who is an engineer is Peter.
    for house in houses:
        if occupation_assignment[house] == occupation_map['engineer'] and name_assignment[house] == name_map['Peter']:
            continue
        else:
            return False
    
    return True

# Generate all possible permutations of names, occupations, and hobbies
for name_perm in itertools.permutations(names):
    for occupation_perm in itertools.permutations(occupations):
        for hobby_perm in itertools.permutations(hobbies):
            name_assignment = {house: name_map[name_perm[i]] for i, house in enumerate(houses)}
            occupation_assignment = {house: occupation_map[occupation_perm[i]] for i, house in enumerate(houses)}
            hobby_assignment = {house: hobby_map[hobby_perm[i]] for i, house in enumerate(houses)}
            
            if check_constraints(name_assignment, occupation_assignment, hobby_assignment):
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": []
                    }
                }
                for house in houses:
                    name = name_perm[house - 1]
                    occupation = occupation_perm[house - 1]
                    hobby = hobby_perm[house - 1]
                    solution["solution"]["rows"].append([str(house), name, occupation, hobby])
                import json
                print(json.dumps(solution))
                break
        else:
            continue
        break
    else:
        continue
    break
else:
    print("No solution found")