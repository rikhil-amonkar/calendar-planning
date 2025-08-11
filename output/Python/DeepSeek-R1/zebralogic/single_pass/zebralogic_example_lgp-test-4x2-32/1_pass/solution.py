import itertools
import json

def main():
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']
    
    for name_perm in itertools.permutations(names):
        for pet_perm in itertools.permutations(pets):
            candidate = []
            for i in range(4):
                candidate.append({
                    'House': i+1,
                    'Name': name_perm[i],
                    'Pet': pet_perm[i]
                })
            
            if candidate[0]['Name'] == 'Eric':
                continue
                
            if candidate[0]['Name'] == 'Alice':
                continue
                
            eric_house = None
            for house in candidate:
                if house['Name'] == 'Eric':
                    eric_house = house
                    break
            if eric_house['Pet'] != 'bird':
                continue
                
            arnold_house = None
            for house in candidate:
                if house['Name'] == 'Arnold':
                    arnold_house = house
                    break
            if arnold_house['Pet'] != 'fish':
                continue
                
            alice_index = None
            dog_index = None
            for idx, house in enumerate(candidate):
                if house['Name'] == 'Alice':
                    alice_index = idx
                if house['Pet'] == 'dog':
                    dog_index = idx
            if dog_index <= alice_index:
                continue
                
            peter_index = None
            fish_index = None
            for idx, house in enumerate(candidate):
                if house['Name'] == 'Peter':
                    peter_index = idx
                if house['Pet'] == 'fish':
                    fish_index = idx
            if abs(peter_index - fish_index) != 2:
                continue
                
            solution = {
                "solution": {
                    "header": ["House", "Name", "Pet"],
                    "rows": []
                }
            }
            for house in candidate:
                solution["solution"]["rows"].append([
                    str(house['House']),
                    house['Name'],
                    house['Pet']
                ])
            
            print(json.dumps(solution, indent=2))
            return
    
    print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()