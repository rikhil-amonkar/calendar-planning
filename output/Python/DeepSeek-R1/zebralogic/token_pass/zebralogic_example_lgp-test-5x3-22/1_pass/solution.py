import itertools
import json

def main():
    # Fixed assignments
    nationalities = [None] * 5
    nationalities[0] = 'swede'
    nationalities[2] = 'norwegian'
    
    smoothies = [None] * 5
    smoothies[1] = 'dragonfruit'
    smoothies[2] = 'watermelon'
    
    names = [None] * 5
    names[2] = 'Alice'
    
    # Available attributes for assignment
    available_names = ['Arnold', 'Eric', 'Bob', 'Peter']
    available_smoothies = ['desert', 'lime', 'cherry']
    available_nationalities = ['german', 'dane', 'brit']
    
    # Generate all permutations of names for houses 0,1,3,4
    for name_perm in itertools.permutations(available_names):
        # Assign names to houses 0,1,3,4
        names[0] = name_perm[0]
        names[1] = name_perm[1]
        names[3] = name_perm[2]
        names[4] = name_perm[3]
        
        # Check name constraints
        if names[0] == 'Peter':
            continue
        if names[1] == 'Eric':
            continue
        if 'Eric' not in [names[3], names[4]]:
            continue
        
        # Find Bob's house
        bob_house = None
        for i in [0,1,3,4]:
            if names[i] == 'Bob':
                bob_house = i
                break
        if bob_house is None:
            continue
            
        # Set Bob's nationality to dane
        nationalities[bob_house] = 'dane'
        
        # The remaining houses for nationalities (from [1,3,4]) excluding Bob's house
        non_dane_houses = [i for i in [1,3,4] if i != bob_house]
        
        # Generate nationalities for the non-dane houses
        for nat_perm in itertools.permutations(['german', 'brit']):
            # Assign nationalities to non-dane houses
            for idx, house in enumerate(non_dane_houses):
                nationalities[house] = nat_perm[idx]
            
            # Generate smoothie assignments for houses 0,3,4
            for smoothie_perm in itertools.permutations(available_smoothies):
                smoothies[0] = smoothie_perm[0]
                smoothies[3] = smoothie_perm[1]
                smoothies[4] = smoothie_perm[2]
                
                # Check smoothie constraint for house4
                if smoothies[4] == 'desert':
                    continue
                    
                # Check constraint 4: Dane and Brit are adjacent
                brit_house = None
                for i in [1,3,4]:
                    if nationalities[i] == 'brit':
                        brit_house = i
                        break
                if brit_house is None:
                    continue
                if abs(bob_house - brit_house) != 1:
                    continue
                    
                # Check constraint 7: Two houses between Lime and Dane
                lime_house = None
                for i in [0,3,4]:
                    if smoothies[i] == 'lime':
                        lime_house = i
                        break
                if lime_house is None:
                    continue
                if abs(lime_house - bob_house) != 3:
                    continue
                    
                # We found a solution, output it
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "Nationality"],
                        "rows": []
                    }
                }
                for i in range(5):
                    solution["solution"]["rows"].append([
                        str(i+1),
                        names[i],
                        smoothies[i],
                        nationalities[i]
                    ])
                
                print(json.dumps(solution, indent=2))
                return
                
    print("No solution found")

if __name__ == "__main__":
    main()