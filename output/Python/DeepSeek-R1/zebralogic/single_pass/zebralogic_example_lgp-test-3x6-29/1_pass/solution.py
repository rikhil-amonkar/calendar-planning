import itertools
import json

def main():
    # Define the attribute values
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    birthdays = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    hair_colors = ['black', 'brown', 'blonde']
    
    # Generate all permutations for each attribute
    for n_perm in itertools.permutations(names):
        for a_perm in itertools.permutations(animals):
            for b_perm in itertools.permutations(birthdays):
                for h_perm in itertools.permutations(hobbies):
                    for d_perm in itertools.permutations(drinks):
                        for c_perm in itertools.permutations(hair_colors):
                            # Check fixed constraints on specific houses
                            if n_perm[0] == 'Eric':  # Eric not in first house
                                continue
                            if a_perm[1] != 'cat':   # Cat lover in second house
                                continue
                            if b_perm[2] != 'april': # April birthday in third house
                                continue
                            if c_perm[1] != 'brown': # Cat lover has brown hair
                                continue
                            if h_perm[1] != 'cooking': # Brown hair implies cooking
                                continue
                            
                            # Constraint 5: Blonde hair left of milk drinker
                            idx_blonde = None
                            idx_milk = None
                            for i in range(3):
                                if c_perm[i] == 'blonde':
                                    idx_blonde = i
                                if d_perm[i] == 'milk':
                                    idx_milk = i
                            if idx_blonde is None or idx_milk is None or idx_blonde >= idx_milk:
                                continue
                            
                            # Constraint 6: Gardening hobby and milk drink same house
                            gardening_index = None
                            for i in range(3):
                                if h_perm[i] == 'gardening':
                                    gardening_index = i
                                    break
                            if gardening_index is None or d_perm[gardening_index] != 'milk':
                                continue
                            
                            # Constraint 8: Arnold is bird keeper
                            arnold_index = None
                            for i in range(3):
                                if n_perm[i] == 'Arnold':
                                    arnold_index = i
                                    break
                            if arnold_index is None or a_perm[arnold_index] != 'bird':
                                continue
                            
                            # Constraint 9: Water drinker is photography enthusiast
                            water_index = None
                            for i in range(3):
                                if d_perm[i] == 'water':
                                    water_index = i
                                    break
                            if water_index is None or h_perm[water_index] != 'photography':
                                continue
                            
                            # Constraint 10: September birthday directly left of Arnold
                            sept_index = None
                            for i in range(3):
                                if b_perm[i] == 'sept':
                                    sept_index = i
                                    break
                            if sept_index is None or sept_index + 1 != arnold_index:
                                continue
                            
                            # Build the solution rows
                            rows = []
                            for i in range(3):
                                row = [str(i+1), n_perm[i], a_perm[i], b_perm[i], h_perm[i], d_perm[i], c_perm[i]]
                                rows.append(row)
                            
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                    "rows": rows
                                }
                            }
                            
                            # Output the solution as JSON
                            print(json.dumps(solution))
                            return
    
    # If no solution found, output an empty solution (though the puzzle should have one)
    print(json.dumps({"solution": {"header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"], "rows": []}}))

if __name__ == "__main__":
    main()