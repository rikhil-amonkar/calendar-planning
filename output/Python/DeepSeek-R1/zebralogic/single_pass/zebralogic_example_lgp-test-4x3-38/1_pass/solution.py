import itertools
import json

def main():
    # Initialize attributes for houses 1 to 4 (index 1 to 4)
    names = [None] * 5
    mothers = [None] * 5
    flowers = [None] * 5
    
    # Fixed assignments from clues
    names[3] = 'Alice'       # Clue 8
    mothers[3] = 'Kailyn'    # Clue 1
    flowers[2] = 'lilies'    # Clue 7 (directly left of Alice in house 3)
    
    # Remaining values to assign
    remaining_names = ['Peter', 'Arnold', 'Eric']
    remaining_mothers = ['Holly', 'Janelle', 'Aniya']
    remaining_flowers = ['carnations', 'roses', 'daffodils']  # For houses 1, 3, 4
    
    # Generate all permutations for the remaining values
    for p_name in itertools.permutations(remaining_names):
        names[1] = p_name[0]
        names[2] = p_name[1]
        names[4] = p_name[2]
        
        for p_mother in itertools.permutations(remaining_mothers):
            mothers[1] = p_mother[0]
            mothers[2] = p_mother[1]
            mothers[4] = p_mother[2]
            
            for p_flower in itertools.permutations(remaining_flowers):
                flowers[1] = p_flower[0]
                flowers[3] = p_flower[1]  # House 3
                flowers[4] = p_flower[2]  # House 4
                
                # Build mappings for constraint checks
                name_to_house = {name: house for house, name in enumerate(names) if name is not None}
                mother_to_house = {mother: house for house, mother in enumerate(mothers) if mother is not None}
                flower_to_house = {flower: house for house, flower in enumerate(flowers) if flower is not None}
                
                # Check constraints
                try:
                    # Clue 4: Eric loves daffodils
                    if flowers[name_to_house['Eric']] != 'daffodils':
                        continue
                    
                    # Clue 5: Arnold's mother is Holly
                    if mothers[name_to_house['Arnold']] != 'Holly':
                        continue
                    
                    # Clue 2: Janelle is right of Arnold
                    if mother_to_house['Janelle'] <= name_to_house['Arnold']:
                        continue
                    
                    # Clue 3: Peter is right of carnations
                    if name_to_house['Peter'] <= flower_to_house['carnations']:
                        continue
                    
                    # Clue 6: Carnations right of Holly
                    if flower_to_house['carnations'] <= mother_to_house['Holly']:
                        continue
                    
                except KeyError:
                    continue  # Skip if any required key is missing
                
                # All constraints satisfied, build solution
                solution_rows = []
                for house in range(1, 5):
                    solution_rows.append([str(house), names[house], mothers[house], flowers[house]])
                
                solution_dict = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Flower"],
                        "rows": solution_rows
                    }
                }
                
                # Output the solution as JSON
                print(json.dumps(solution_dict))
                return
    
    # If no solution found (shouldn't happen for valid puzzle)
    print(json.dumps({"solution": {"header": ["House", "Name", "Mother", "Flower"], "rows": []}}))

if __name__ == "__main__":
    main()