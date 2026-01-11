import itertools
import json

# Define the attributes
names = ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice']
animals = ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog']
occupations = ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor']
favorite_sports = ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming']
heights = ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']

# Function to check constraints
def check_constraints(house_data):
    # Unpack the data
    names_order, animals_order, occupations_order, sports_order, heights_order = house_data
    
    # Clue 1: Engineer -> Dog
    if occupations_order.index('engineer') != animals_order.index('dog'):
        return False
    
    # Clue 2: Average Height -> Somewhere left of Short
    if heights_order.index('average') >= heights_order.index('short'):
        return False
    
    # Clue 3: Average Height -> Directly left of Rabbit Owner
    avg_height_index = heights_order.index('average')
    rabbit_owner_index = animals_order.index('rabbit')
    if avg_height_index + 1 != rabbit_owner_index:
        return False
    
    # Clue 4: Tall -> Somewhere left of Very Short
    if heights_order.index('tall') >= heights_order.index('very short'):
        return False
    
    # Clue 5: Arnold -> Cat
    if names_order.index('Arnold') != animals_order.index('cat'):
        return False
    
    # Clue 6: Teacher -> Horse
    if occupations_order.index('teacher') != animals_order.index('horse'):
        return False
    
    # Clue 7: Carol -> Soccer
    if names_order.index('Carol') != sports_order.index('soccer'):
        return False
    
    # Clue 8: Tall -> Volleyball
    if heights_order.index('tall') != sports_order.index('volleyball'):
        return False
    
    # Clue 9: Lawyer -> House 5
    if occupations_order[4] != 'lawyer':
        return False
    
    # Clue 10: Teacher -> Tennis
    if occupations_order.index('teacher') != sports_order.index('tennis'):
        return False
    
    # Clue 11: Average Height -> Swimming
    if heights_order.index('average') != sports_order.index('swimming'):
        return False
    
    # Clue 12: Baseball -> Directly left of Engineer
    baseball_index = sports_order.index('baseball')
    engineer_index = occupations_order.index('engineer')
    if baseball_index + 1 != engineer_index:
        return False
    
    # Clue 13: Peter -> Nurse
    if names_order.index('Peter') != occupations_order.index('nurse'):
        return False
    
    # Clue 14: Bob -> Somewhere right of Artist
    bob_index = names_order.index('Bob')
    artist_index = occupations_order.index('artist')
    if bob_index <= artist_index:
        return False
    
    # Clue 15: Teacher -> Directly left of Soccer
    teacher_index = occupations_order.index('teacher')
    soccer_index = sports_order.index('soccer')
    if teacher_index + 1 != soccer_index:
        return False
    
    # Clue 16: Rabbit Owner -> Alice
    if names_order[rabbit_owner_index] != 'Alice':
        return False
    
    # Clue 17: Fish -> Carol
    if names_order[animals_order.index('fish')] != 'Carol':
        return False
    
    # Clue 18: Baseball -> House 1
    if sports_order[0] != 'baseball':
        return False
    
    # Clue 19: Cat Lover -> Somewhere right of Very Short
    cat_lover_index = animals_order.index('cat')
    very_short_index = heights_order.index('very short')
    if cat_lover_index <= very_short_index:
        return False
    
    # Clue 20: Super Tall -> House 5
    if heights_order[4] != 'super tall':
        return False
    
    return True

# Generate all permutations and check constraints
for names_perm in itertools.permutations(names):
    for animals_perm in itertools.permutations(animals):
        for occupations_perm in itertools.permutations(occupations):
            for sports_perm in itertools.permutations(favorite_sports):
                for heights_perm in itertools.permutations(heights):
                    house_data = (names_perm, animals_perm, occupations_perm, sports_perm, heights_perm)
                    if check_constraints(house_data):
                        # Format the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                                "rows": []
                            }
                        }
                        for i in range(6):
                            solution["solution"]["rows"].append([
                                str(i+1),
                                names_perm[i],
                                animals_perm[i],
                                occupations_perm[i],
                                sports_perm[i],
                                heights_perm[i]
                            ])
                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
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