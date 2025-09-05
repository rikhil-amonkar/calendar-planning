import json
from z3 import *

def main():
    solver = Solver()
    
    # Define the categories and their values
    categories = {
        'Name': ['Eric', 'Peter', 'Arnold', 'Alice'],
        'Smoothie': ['dragonfruit', 'cherry', 'desert', 'watermelon'],
        'Cigar': ['blue master', 'pall mall', 'dunhill', 'prince'],
        'Height': ['tall', 'average', 'short', 'very short'],
        'PhoneModel': ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    }
    
    # Create enum sorts and mappings for each category
    enums = {}
    mappings = {}
    reverse_mappings = {}
    
    for cat, values in categories.items():
        symbols = [v.replace(' ', '_') for v in values]
        sort, constants = EnumSort(cat, symbols)
        enums[cat] = (sort, constants)
        mapping = {}
        for v, c in zip(values, constants):
            mapping[v] = c
        mappings[cat] = mapping
        reverse_mapping = {c: v for v, c in mapping.items()}
        reverse_mappings[cat] = reverse_mapping

    # Define attributes for each house (1-4)
    attributes = {}
    for cat in categories:
        sort = enums[cat][0]
        att_list = [Const(f'{cat}_{i}', sort) for i in range(1, 5)]
        attributes[cat] = att_list
    
    # Add distinct constraints for each attribute
    for att_list in attributes.values():
        solver.add(Distinct(att_list))
    
    # Get attribute lists
    names = attributes['Name']
    smoothies = attributes['Smoothie']
    cigars = attributes['Cigar']
    heights = attributes['Height']
    phones = attributes['PhoneModel']
    
    # Get constant mappings
    name_map = mappings['Name']
    smoothie_map = mappings['Smoothie']
    cigar_map = mappings['Cigar']
    height_map = mappings['Height']
    phone_map = mappings['PhoneModel']
    
    # Helper function to get house index (0-based)
    def get_index(lst, val):
        return If(lst[0] == val, 0,
               If(lst[1] == val, 1,
               If(lst[2] == val, 2, 3)))
    
    # Clue 1: Dragonfruit smoothie lover is Eric
    for i in range(4):
        solver.add(Implies(smoothies[i] == smoothie_map['dragonfruit'], 
                          names[i] == name_map['Eric']))
    
    # Clue 2: Dunhill smoker likes Cherry smoothie
    for i in range(4):
        solver.add(Implies(cigars[i] == cigar_map['dunhill'], 
                          smoothies[i] == smoothie_map['cherry']))
    
    # Clue 3: Samsung directly left of iPhone
    for i in range(3):
        solver.add(Implies(phones[i] == phone_map['samsung galaxy s21'], 
                          phones[i+1] == phone_map['iphone 13']))
    
    # Clue 4: Dunhill right of very short
    dunhill_idx = get_index(cigars, cigar_map['dunhill'])
    very_short_idx = get_index(heights, height_map['very short'])
    solver.add(dunhill_idx > very_short_idx)
    
    # Clue 5: Watermelon right of Desert
    watermelon_idx = get_index(smoothies, smoothie_map['watermelon'])
    desert_idx = get_index(smoothies, smoothie_map['desert'])
    solver.add(watermelon_idx > desert_idx)
    
    # Clue 6: Prince smoker uses OnePlus 9
    for i in range(4):
        solver.add(Implies(cigars[i] == cigar_map['prince'], 
                          phones[i] == phone_map['oneplus 9']))
    
    # Clue 7: Tall in third house
    solver.add(heights[2] == height_map['tall'])
    
    # Clue 8: Very short uses iPhone 13
    for i in range(4):
        solver.add(Implies(heights[i] == height_map['very short'], 
                          phones[i] == phone_map['iphone 13']))
    
    # Clue 9: Blue Master not in first house
    solver.add(cigars[0] != cigar_map['blue master'])
    
    # Clue 10: Dunhill smoker is short
    for i in range(4):
        solver.add(Implies(cigars[i] == cigar_map['dunhill'], 
                          heights[i] == height_map['short']))
    
    # Clue 11: Peter not in third house
    solver.add(names[2] != name_map['Peter'])
    
    # Clue 12: Arnold uses Google Pixel 6
    for i in range(4):
        solver.add(Implies(names[i] == name_map['Arnold'], 
                          phones[i] == phone_map['google pixel 6']))
    
    # Clue 13: Dragonfruit lover smokes Pall Mall
    for i in range(4):
        solver.add(Implies(smoothies[i] == smoothie_map['dragonfruit'], 
                          cigars[i] == cigar_map['pall mall']))
    
    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = model.eval(names[i])
            smoothie_val = model.eval(smoothies[i])
            cigar_val = model.eval(cigars[i])
            height_val = model.eval(heights[i])
            phone_val = model.eval(phones[i])
            
            name_str = reverse_mappings['Name'][name_val]
            smoothie_str = reverse_mappings['Smoothie'][smoothie_val]
            cigar_str = reverse_mappings['Cigar'][cigar_val]
            height_str = reverse_mappings['Height'][height_val]
            phone_str = reverse_mappings['PhoneModel'][phone_val]
            
            rows.append([house_num, name_str, smoothie_str, cigar_str, height_str, phone_str])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()