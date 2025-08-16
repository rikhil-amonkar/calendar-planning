import json
import copy

def main():
    attributes = ['Name', 'Birthday', 'Food', 'Height', 'CarModel']
    name_values = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
    birthday_values = ['feb', 'mar', 'sept', 'jan', 'may', 'april']
    food_values = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    height_values = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
    carmodel_values = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']
    
    attr_index = {attr: i for i, attr in enumerate(attributes)}
    value_sets = [name_values, birthday_values, food_values, height_values, carmodel_values]
    
    domains = [[set(value_sets[att_idx]) for att_idx in range(5)] for _ in range(6)]
    
    def apply_clue_and_all_diff(domains):
        changed = False
        for att_idx in range(5):
            fixed_values = {}
            for house in range(6):
                if len(domains[house][att_idx]) == 1:
                    val = next(iter(domains[house][att_idx]))
                    fixed_values[val] = house
            for house in range(6):
                if len(domains[house][att_idx]) > 1:
                    for val, fixed_house in fixed_values.items():
                        if house != fixed_house and val in domains[house][att_idx]:
                            domains[house][att_idx].remove(val)
                            changed = True
        return changed
    
    def apply_easy_clues(domains):
        changed = False
        # Clue 2: Ford F150 in house5 (index4)
        if domains[4][4] != {'ford f150'}:
            domains[4][4] = {'ford f150'}
            changed = True
        # Clue 19: very short in house4 (index3)
        if domains[3][3] != {'very short'}:
            domains[3][3] = {'very short'}
            changed = True
        # Clue 6: BMW not in house3 (index2)
        if 'bmw 3 series' in domains[2][4]:
            domains[2][4].remove('bmw 3 series')
            changed = True
        # Clue 14: stew not in house3 (index2)
        if 'stew' in domains[2][2]:
            domains[2][2].remove('stew')
            changed = True
        # Clue 1: Honda Civic owner is short
        for i in range(6):
            if 'honda civic' in domains[i][4]:
                new_set = domains[i][3] & {'short'}
                if new_set != domains[i][3]:
                    domains[i][3] = new_set
                    changed = True
            if 'short' in domains[i][3]:
                new_set = domains[i][4] & {'honda civic'}
                if new_set != domains[i][4]:
                    domains[i][4] = new_set
                    changed = True
        # Clue 12: very tall owns Toyota Camry
        for i in range(6):
            if 'very tall' in domains[i][3]:
                new_set = domains[i][4] & {'toyota camry'}
                if new_set != domains[i][4]:
                    domains[i][4] = new_set
                    changed = True
            if 'toyota camry' in domains[i][4]:
                new_set = domains[i][3] & {'very tall'}
                if new_set != domains[i][3]:
                    domains[i][3] = new_set
                    changed = True
        # Clue 17: tall is Bob
        for i in range(6):
            if 'tall' in domains[i][3]:
                new_set = domains[i][0] & {'Bob'}
                if new_set != domains[i][0]:
                    domains[i][0] = new_set
                    changed = True
            if 'Bob' in domains[i][0]:
                new_set = domains[i][3] & {'tall'}
                if new_set != domains[i][3]:
                    domains[i][3] = new_set
                    changed = True
        # Clue 20: March birthday is short
        for i in range(6):
            if 'mar' in domains[i][1]:
                new_set = domains[i][3] & {'short'}
                if new_set != domains[i][3]:
                    domains[i][3] = new_set
                    changed = True
            if 'short' in domains[i][3]:
                new_set = domains[i][1] & {'mar'}
                if new_set != domains[i][1]:
                    domains[i][1] = new_set
                    changed = True
        # Clue 21: Carol owns Tesla
        for i in range(6):
            if 'Carol' in domains[i][0]:
                new_set = domains[i][4] & {'tesla model 3'}
                if new_set != domains[i][4]:
                    domains[i][4] = new_set
                    changed = True
            if 'tesla model 3' in domains[i][4]:
                new_set = domains[i][0] & {'Carol'}
                if new_set != domains[i][0]:
                    domains[i][0] = new_set
                    changed = True
        # Clue 22: Eric has January birthday
        for i in range(6):
            if 'Eric' in domains[i][0]:
                new_set = domains[i][1] & {'jan'}
                if new_set != domains[i][1]:
                    domains[i][1] = new_set
                    changed = True
            if 'jan' in domains[i][1]:
                new_set = domains[i][0] & {'Eric'}
                if new_set != domains[i][0]:
                    domains[i][0] = new_set
                    changed = True
        return changed
    
    changed = True
    while changed:
        changed = False
        changed = apply_easy_clues(domains) or changed
        changed = apply_clue_and_all_diff(domains) or changed
    
    assignment = [[None]*5 for _ in range(6)]
    for house in range(6):
        for att in range(5):
            if len(domains[house][att]) == 1:
                assignment[house][att] = next(iter(domains[house][att]))
    
    def find_unassigned(assignment):
        for house in range(6):
            for att in range(5):
                if assignment[house][att] is None:
                    return (house, att)
        return None
    
    def is_complete(assignment):
        for house in range(6):
            for att in range(5):
                if assignment[house][att] is None:
                    return False
        return True
    
    def check_complex_clues(assignment):
        # Clue 3: stir fry left of Eric
        stir_fry_house = None
        eric_house = None
        for i in range(6):
            if assignment[i][attr_index['Food']] == 'stir fry':
                stir_fry_house = i
            if assignment[i][attr_index['Name']] == 'Eric':
                eric_house = i
        if stir_fry_house is None or eric_house is None or stir_fry_house >= eric_house:
            return False
        
        # Clue 4: May birthday left of Carol
        may_house = None
        carol_house = None
        for i in range(6):
            if assignment[i][attr_index['Birthday']] == 'may':
                may_house = i
            if assignment[i][attr_index['Name']] == 'Carol':
                carol_house = i
        if may_house is None or carol_house is None or may_house >= carol_house:
            return False
        
        # Clue 5: very short left of April birthday
        very_short_house = None
        april_house = None
        for i in range(6):
            if assignment[i][attr_index['Height']] == 'very short':
                very_short_house = i
            if assignment[i][attr_index['Birthday']] == 'april':
                april_house = i
        if very_short_house is None or april_house is None or very_short_house >= april_house:
            return False
        
        # Clue 7: two houses between stir fry and pizza
        stir_fry_house = None
        pizza_house = None
        for i in range(6):
            if assignment[i][attr_index['Food']] == 'stir fry':
                stir_fry_house = i
            if assignment[i][attr_index['Food']] == 'pizza':
                pizza_house = i
        if stir_fry_house is None or pizza_house is None or abs(stir_fry_house - pizza_house) != 3:
            return False
        
        # Clue 8: soup directly left of Eric
        soup_house = None
        eric_house = None
        for i in range(6):
            if assignment[i][attr_index['Food']] == 'soup':
                soup_house = i
            if assignment[i][attr_index['Name']] == 'Eric':
                eric_house = i
        if soup_house is None or eric_house is None or soup_house != eric_house - 1:
            return False
        
        # Clue 9: spaghetti and May birthday adjacent
        spaghetti_house = None
        may_house = None
        for i in range(6):
            if assignment[i][attr_index['Food']] == 'spaghetti':
                spaghetti_house = i
            if assignment[i][attr_index['Birthday']] == 'may':
                may_house = i
        if spaghetti_house is None or may_house is None or abs(spaghetti_house - may_house) != 1:
            return False
        
        # Clue 10: Alice directly left of BMW owner
        alice_house = None
        bmw_house = None
        for i in range(6):
            if assignment[i][attr_index['Name']] == 'Alice':
                alice_house = i
            if assignment[i][attr_index['CarModel']] == 'bmw 3 series':
                bmw_house = i
        if alice_house is None or bmw_house is None or alice_house != bmw_house - 1:
            return False
        
        # Clue 11: Tesla left of tall
        tesla_house = None
        tall_house = None
        for i in range(6):
            if assignment[i][attr_index['CarModel']] == 'tesla model 3':
                tesla_house = i
            if assignment[i][attr_index['Height']] == 'tall':
                tall_house = i
        if tesla_house is None or tall_house is None or tesla_house >= tall_house:
            return False
        
        # Clue 13: Peter directly left of pizza
        peter_house = None
        pizza_house = None
        for i in range(6):
            if assignment[i][attr_index['Name']] == 'Peter':
                peter_house = i
            if assignment[i][attr_index['Food']] == 'pizza':
                pizza_house = i
        if peter_house is None or pizza_house is None or peter_house != pizza_house - 1:
            return False
        
        # Clue 15: one house between September and very short
        sept_house = None
        very_short_house = None
        for i in range(6):
            if assignment[i][attr_index['Birthday']] == 'sept':
                sept_house = i
            if assignment[i][attr_index['Height']] == 'very short':
                very_short_house = i
        if sept_house is None or very_short_house is None or abs(sept_house - very_short_house) != 2:
            return False
        
        # Clue 16: one house between March and super tall
        mar_house = None
        super_tall_house = None
        for i in range(6):
            if assignment[i][attr_index['Birthday']] == 'mar':
                mar_house = i
            if assignment[i][attr_index['Height']] == 'super tall':
                super_tall_house = i
        if mar_house is None or super_tall_house is None or abs(mar_house - super_tall_house) != 2:
            return False
        
        # Clue 18: May birthday right of Alice
        may_house = None
        alice_house = None
        for i in range(6):
            if assignment[i][attr_index['Birthday']] == 'may':
                may_house = i
            if assignment[i][attr_index['Name']] == 'Alice':
                alice_house = i
        if may_house is None or alice_house is None or may_house <= alice_house:
            return False
        
        return True
    
    def backtrack(assignment, domains):
        unassigned = find_unassigned(assignment)
        if unassigned is None:
            if is_complete(assignment) and check_complex_clues(assignment):
                return assignment
            return None
        
        house, att = unassigned
        for value in list(domains[house][att]):
            new_assignment = copy.deepcopy(assignment)
            new_domains = copy.deepcopy(domains)
            new_assignment[house][att] = value
            new_domains[house][att] = {value}
            valid = True
            
            for other_house in range(6):
                if other_house != house:
                    if value in new_domains[other_house][att]:
                        new_domains[other_house][att].remove(value)
                        if len(new_domains[other_house][att]) == 0:
                            valid = False
                            break
            if not valid:
                continue
            
            result = backtrack(new_assignment, new_domains)
            if result is not None:
                return result
        return None
    
    final_assignment = backtrack(assignment, domains)
    
    if final_assignment is None:
        return
    
    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": []
        }
    }
    for house in range(6):
        row = [str(house+1)]
        for att in range(5):
            row.append(final_assignment[house][att])
        output["solution"]["rows"].append(row)
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()