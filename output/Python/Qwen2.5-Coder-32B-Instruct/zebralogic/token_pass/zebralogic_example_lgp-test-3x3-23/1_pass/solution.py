import itertools
import json

def solve_puzzle():
    # Define the domains
    people = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']
    
    # Generate all possible permutations for people, occupations, and hobbies
    people_perms = list(itertools.permutations(people))
    occupations_perms = list(itertools.permutations(occupations))
    hobbies_perms = list(itertools.permutations(hobbies))
    
    # Iterate over all permutations and check the constraints
    for people_perm in people_perms:
        for occupations_perm in occupations_perms:
            for hobbies_perm in hobbies_perms:
                # Create a mapping of house number to attributes
                house_map = {
                    1: {'name': people_perm[0], 'occupation': occupations_perm[0], 'hobby': hobbies_perm[0]},
                    2: {'name': people_perm[1], 'occupation': occupations_perm[1], 'hobby': hobbies_perm[1]},
                    3: {'name': people_perm[2], 'occupation': occupations_perm[2], 'hobby': hobbies_perm[2]}
                }
                
                # Check Clue 5: The person who is an engineer is Peter.
                if house_map[1]['name'] == 'Peter' and house_map[1]['occupation'] != 'engineer':
                    continue
                if house_map[2]['name'] == 'Peter' and house_map[2]['occupation'] != 'engineer':
                    continue
                if house_map[3]['name'] == 'Peter' and house_map[3]['occupation'] != 'engineer':
                    continue
                
                # Check Clue 4: The photography enthusiast is the person who is a teacher.
                if any(house['hobby'] == 'photography' and house['occupation'] != 'teacher' for house in house_map.values()):
                    continue
                if any(house['occupation'] == 'teacher' and house['hobby'] != 'photography' for house in house_map.values()):
                    continue
                
                # Check Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
                if (house_map[1]['occupation'] == 'doctor' and house_map[1]['hobby'] == 'gardening') or \
                   (house_map[2]['occupation'] == 'doctor' and house_map[1]['hobby'] == 'gardening') or \
                   (house_map[3]['occupation'] == 'doctor' and (house_map[1]['hobby'] == 'gardening' or house_map[2]['hobby'] == 'gardening')):
                    continue
                
                # Check Clue 2: The person who loves cooking is directly left of the person who is a teacher.
                if (house_map[1]['hobby'] == 'cooking' and house_map[2]['occupation'] != 'teacher') or \
                   (house_map[2]['hobby'] == 'cooking' and house_map[3]['occupation'] != 'teacher'):
                    continue
                
                # Check Clue 1: The person who is a doctor and Eric are next to each other.
                if (house_map[1]['name'] == 'Eric' and house_map[2]['occupation'] != 'doctor') or \
                   (house_map[2]['name'] == 'Eric' and (house_map[1]['occupation'] != 'doctor' and house_map[3]['occupation'] != 'doctor')) or \
                   (house_map[3]['name'] == 'Eric' and house_map[2]['occupation'] != 'doctor'):
                    continue
                
                # If all checks pass, we have found the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": [
                            [str(house), house_map[house]['name'], house_map[house]['occupation'], house_map[house]['hobby']]
                            for house in range(1, 4)
                        ]
                    }
                }
                
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())