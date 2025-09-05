import itertools
import json

def main():
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']
    
    for name_perm in itertools.permutations(names):
        # Check constraints on names: Eric and Alice not in first house
        if name_perm[0] == 'Eric' or name_perm[0] == 'Alice':
            continue
            
        for pet_perm in itertools.permutations(pets):
            assignment = []
            for i in range(4):
                assignment.append({
                    'house': i+1,
                    'name': name_perm[i],
                    'pet': pet_perm[i]
                })
            
            # Constraint 3: Eric has bird
            eric_house = next((h for h in assignment if h['name'] == 'Eric'), None)
            if eric_house is None or eric_house['pet'] != 'bird':
                continue
                
            # Constraint 6: Arnold has fish
            arnold_house = next((h for h in assignment if h['name'] == 'Arnold'), None)
            if arnold_house is None or arnold_house['pet'] != 'fish':
                continue
                
            # Constraint 4: One house between fish and Peter
            fish_house = arnold_house['house']
            peter_house = next(h['house'] for h in assignment if h['name'] == 'Peter')
            if abs(fish_house - peter_house) != 2:
                continue
                
            # Constraint 1: Dog owner is right of Alice
            alice_house = next(h for h in assignment if h['name'] == 'Alice')
            dog_house = next(h for h in assignment if h['pet'] == 'dog')
            if dog_house['house'] <= alice_house['house']:
                continue
                
            # All constraints satisfied, build solution
            rows = []
            for house in sorted(assignment, key=lambda x: x['house']):
                rows.append([str(house['house']), house['name'], house['pet']])
                
            result = {
                "solution": {
                    "header": ["House", "Name", "Pet"],
                    "rows": rows
                }
            }
            
            print(json.dumps(result, indent=2))
            return
            
    print('No solution found')

if __name__ == '__main__':
    main()