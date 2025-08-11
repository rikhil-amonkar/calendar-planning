import itertools
import json

def main():
    names_list = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies_list = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    
    for names in itertools.permutations(names_list):
        eric_index = names.index('Eric')
        bob_index = names.index('Bob')
        alice_index = names.index('Alice')
        
        if eric_index == 2 or bob_index == 2:
            continue
            
        if bob_index <= eric_index:
            continue
            
        remaining_houses = [i for i in range(5) if i not in [2, eric_index, bob_index]]
        if len(remaining_houses) != 2:
            continue
            
        for animals_remaining in itertools.permutations(['dog', 'fish']):
            animal_assignment = [None] * 5
            animal_assignment[eric_index] = 'cat'
            animal_assignment[bob_index] = 'bird'
            animal_assignment[2] = 'horse'
            animal_assignment[remaining_houses[0]] = animals_remaining[0]
            animal_assignment[remaining_houses[1]] = animals_remaining[1]
            
            dog_index = None
            for i in remaining_houses:
                if animal_assignment[i] == 'dog':
                    dog_index = i
                    break
            if dog_index is None:
                continue
                
            if dog_index == 4:
                continue
                
            next_index = dog_index + 1
            if next_index == bob_index:
                continue
                
            smoothie_assignment = [None] * 5
            smoothie_assignment[dog_index] = 'desert'
            smoothie_assignment[next_index] = 'lime'
            smoothie_assignment[bob_index] = 'watermelon'
            
            remaining_smoothie_houses = [i for i in range(5) if smoothie_assignment[i] is None]
            remaining_smoothies = [s for s in smoothies_list if s not in ['desert', 'lime', 'watermelon']]
            
            for smoothies_remaining in itertools.permutations(remaining_smoothies):
                for idx, s_val in zip(remaining_smoothie_houses, smoothies_remaining):
                    smoothie_assignment[idx] = s_val
                    
                found_cherry = False
                for i in range(4):
                    if smoothie_assignment[i] == 'cherry' and names[i+1] == 'Peter':
                        found_cherry = True
                        break
                if not found_cherry:
                    continue
                    
                if dog_index + 3 < 5:
                    brit_index = dog_index + 3
                elif dog_index - 3 >= 0:
                    brit_index = dog_index - 3
                else:
                    continue
                    
                nationality_assignment = [None] * 5
                nationality_assignment[2] = 'dane'
                nationality_assignment[alice_index] = 'norwegian'
                nationality_assignment[dog_index-1] = 'swede'
                nationality_assignment[brit_index] = 'brit'
                
                assigned_nat_indices = {2, alice_index, dog_index-1, brit_index}
                if len(assigned_nat_indices) != 4:
                    continue
                    
                remaining_nat_houses = [i for i in range(5) if i not in assigned_nat_indices]
                if len(remaining_nat_houses) != 1:
                    continue
                german_index = remaining_nat_houses[0]
                nationality_assignment[german_index] = 'german'
                
                rows = []
                for i in range(5):
                    rows.append([
                        str(i+1),
                        names[i],
                        smoothie_assignment[i],
                        animal_assignment[i],
                        nationality_assignment[i]
                    ])
                
                solution_dict = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                        "rows": rows
                    }
                }
                
                print(json.dumps(solution_dict, indent=2))
                return
                
    print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()