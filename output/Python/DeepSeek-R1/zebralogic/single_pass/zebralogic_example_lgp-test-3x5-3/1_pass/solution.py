import itertools
import json

def main():
    names_list = ['Eric', 'Peter', 'Arnold']
    smoothies_list = ['cherry', 'watermelon', 'desert']
    flowers_list = ['carnations', 'lilies', 'daffodils']
    animals_list = ['cat', 'horse', 'bird']
    hobbies_list = ['photography', 'cooking', 'gardening']
    
    def check(candidate):
        names, smoothies, flowers, animals, hobbies = candidate
        
        # Clue 8: The photography enthusiast is Eric.
        for i in range(3):
            if hobbies[i] == 'photography':
                if names[i] != 'Eric':
                    return False
        
        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
        for i in range(3):
            if animals[i] == 'bird':
                if smoothies[i] != 'cherry':
                    return False
        
        # Clue 3: The person who loves cooking is the Desert smoothie lover.
        for i in range(3):
            if hobbies[i] == 'cooking':
                if smoothies[i] != 'desert':
                    return False
        
        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
        for i in range(3):
            if hobbies[i] == 'gardening':
                if flowers[i] != 'carnations':
                    return False
        
        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
        for i in range(3):
            if flowers[i] == 'daffodils':
                if smoothies[i] != 'desert':
                    return False
        
        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
        for i in range(3):
            if smoothies[i] == 'watermelon':
                if animals[i] != 'horse':
                    return False
        
        # Clue 5: The person who loves cooking is directly left of Peter.
        cooking_index = None
        for i in range(3):
            if hobbies[i] == 'cooking':
                cooking_index = i
                break
        if cooking_index is None:
            return False
        if cooking_index == 2:  # Last house, no house to the right
            return False
        if names[cooking_index + 1] != 'Peter':
            return False
        
        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
        horse_index = None
        photo_index = None
        for i in range(3):
            if animals[i] == 'horse':
                horse_index = i
            if hobbies[i] == 'photography':
                photo_index = i
        if horse_index is None or photo_index is None:
            return False
        if abs(horse_index - photo_index) != 1:
            return False
        
        return True

    for names in itertools.permutations(names_list):
        for smoothies in itertools.permutations(smoothies_list):
            for flowers in itertools.permutations(flowers_list):
                for animals in itertools.permutations(animals_list):
                    for hobbies in itertools.permutations(hobbies_list):
                        candidate = (names, smoothies, flowers, animals, hobbies)
                        if check(candidate):
                            rows = []
                            for i in range(3):
                                row = [str(i+1), names[i], smoothies[i], flowers[i], animals[i], hobbies[i]]
                                rows.append(row)
                            solution_dict = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                    "rows": rows
                                }
                            }
                            print(json.dumps(solution_dict))
                            return
    print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()