import itertools
import json

def main():
    fixed_names = {2: 'Eric', 6: 'Carol'}
    fixed_music = {3: 'hip hop', 6: 'country'}
    
    remaining_houses_names = [1, 3, 4, 5]
    remaining_names = ['Arnold', 'Peter', 'Alice', 'Bob']
    
    remaining_houses_music = [1, 2, 4, 5]
    remaining_music = ['jazz', 'pop', 'classical', 'rock']
    
    solution_found = None
    
    for name_perm in itertools.permutations(remaining_names):
        name_assignment = fixed_names.copy()
        for idx, house in enumerate(remaining_houses_names):
            name_assignment[house] = name_perm[idx]
        
        for music_perm in itertools.permutations(remaining_music):
            music_assignment = fixed_music.copy()
            for idx, house in enumerate(remaining_houses_music):
                music_assignment[house] = music_perm[idx]
            
            # Clue 1: Bob is directly left of jazz
            bob_house = None
            for house, name in name_assignment.items():
                if name == 'Bob':
                    bob_house = house
                    break
            jazz_house = None
            for house, music in music_assignment.items():
                if music == 'jazz':
                    jazz_house = house
                    break
            if bob_house is None or jazz_house is None or (bob_house + 1) != jazz_house:
                continue
            
            # Clue 7: Arnold is to the right of pop
            arnold_house = None
            for house, name in name_assignment.items():
                if name == 'Arnold':
                    arnold_house = house
                    break
            pop_house = None
            for house, music in music_assignment.items():
                if music == 'pop':
                    pop_house = house
                    break
            if arnold_house is None or pop_house is None or not (arnold_house > pop_house):
                continue
            
            # Clue 8: Pop music must be Peter
            if name_assignment.get(pop_house) != 'Peter':
                continue
            
            # Clue 10: One house between Peter and Bob
            peter_house = None
            for house, name in name_assignment.items():
                if name == 'Peter':
                    peter_house = house
                    break
            if peter_house is None or abs(peter_house - bob_house) != 2:
                continue
            
            # Clue 11: Rock not in house 5
            if music_assignment.get(5) == 'rock':
                continue
            
            solution_found = (name_assignment, music_assignment)
            break
        
        if solution_found:
            break
    
    if solution_found:
        name_assignment, music_assignment = solution_found
        rows = []
        for house in range(1, 7):
            rows.append([
                str(house),
                name_assignment[house],
                music_assignment[house]
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Music"],
                "rows": rows
            }
        }
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "Music"],
                "rows": []
            }
        }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()