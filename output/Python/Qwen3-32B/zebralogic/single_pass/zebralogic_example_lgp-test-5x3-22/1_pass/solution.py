import itertools
import json

def solve_puzzle():
    # Initialize the lists with known values
    names = [None] * 5
    names[2] = 'Alice'  # House 3 (index 2)
    
    smoothies = [None] * 5
    smoothies[1] = 'dragonfruit'  # House 2 (index 1)
    smoothies[2] = 'watermelon'   # House 3 (index 2)
    
    nationalities = [None] * 5
    nationalities[0] = 'swede'    # House 1 (index 0)
    nationalities[2] = 'norwegian' # House 3 (index 2)
    
    # Possible permutations for names (positions 0,1,3,4)
    name_candidates = ['Arnold', 'Eric', 'Bob', 'Peter']
    for name_perm in itertools.permutations(name_candidates):
        # Check Peter not in first house (index 0)
        if name_perm[0] == 'Peter':
            continue
        names[0] = name_perm[0]
        names[1] = name_perm[1]
        names[3] = name_perm[2]
        names[4] = name_perm[3]
        
        # Possible permutations for smoothies (positions 0, 3, 4)
        smoothie_candidates = ['desert', 'lime', 'cherry']
        for smoothie_perm in itertools.permutations(smoothie_candidates):
            # Check desert not in fifth house (index 4)
            if smoothie_perm[2] == 'desert':
                continue
            smoothies[0] = smoothie_perm[0]
            smoothies[3] = smoothie_perm[1]
            smoothies[4] = smoothie_perm[2]
            
            # Possible permutations for nationalities (positions 1,3,4)
            nationality_candidates = ['german', 'dane', 'brit']
            for nat_perm in itertools.permutations(nationality_candidates):
                nationalities[1] = nat_perm[0]
                nationalities[3] = nat_perm[1]
                nationalities[4] = nat_perm[2]
                
                # Now check all constraints
                
                # Clue 1: Dragonfruit (index 1) is left of Eric.
                eric_house = None
                for i in range(5):
                    if names[i] == 'Eric':
                        eric_house = i
                        break
                if eric_house is None or eric_house <= 1:  # since 1 is index of house 2
                    continue
                
                # Clue 4: Dane and Brit are next to each other
                dane_index = None
                brit_index = None
                for i in range(5):
                    if nationalities[i] == 'dane':
                        dane_index = i
                    if nationalities[i] == 'brit':
                        brit_index = i
                if abs(dane_index - brit_index) != 1:
                    continue
                
                # Clue 7: two houses between Lime and Dane
                lime_index = None
                for i in range(5):
                    if smoothies[i] == 'lime':
                        lime_index = i
                        break
                if abs(lime_index - dane_index) != 3:
                    continue
                
                # Clue 8: Bob is Dane
                bob_index = None
                for i in range(5):
                    if names[i] == 'Bob':
                        bob_index = i
                        break
                if nationalities[bob_index] != 'dane':
                    continue
                
                # If all constraints are met, build the solution
                solution = []
                for i in range(5):
                    house_num = str(i+1)
                    name = names[i]
                    smoothie = smoothies[i]
                    nationality = nationalities[i]
                    solution.append([house_num, name, smoothie, nationality])
                return {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "Nationality"],
                        "rows": solution
                    }
    # If no solution found (unlikely), return empty
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))