import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    people = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']

    # Generate all permutations for each category
    person_permutations = list(itertools.permutations(people))
    education_permutations = list(itertools.permutations(educations))
    occupation_permutations = list(itertools.permutations(occupations))

    # Function to check if a combination satisfies all the clues
    def is_valid(persons, educations, occupations):
        # Clue 3: Peter is the person with a high school diploma
        if educations[persons.index('Peter')] != 'high school':
            return False
        
        # Clue 4: The person who is a doctor is the person with a bachelor's degree
        if educations[occupations.index('doctor')] != 'bachelor':
            return False
        
        # Clue 1: The person who is a teacher is directly left of the person with an associate's degree
        if occupations.index('teacher') + 1 == len(occupations) or \
           educations[occupations.index('teacher') + 1] != 'associate':
            return False
        
        # Clue 2: The person with an associate's degree and Eric are next to each other
        eric_index = persons.index('Eric')
        assoc_index = educations.index('associate')
        if abs(eric_index - assoc_index) != 1:
            return False
        
        return True

    # Find the valid combination
    for persons in person_permutations:
        for educations in education_permutations:
            for occupations in occupation_permutations:
                if is_valid(persons, educations, occupations):
                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Education", "Occupation"],
                            "rows": [
                                [str(i+1), persons[i], educations[i], occupations[i]] for i in range(3)
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())