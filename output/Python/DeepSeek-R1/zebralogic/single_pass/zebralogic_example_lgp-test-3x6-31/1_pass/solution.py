import itertools
import json

def satisfies(houses):
    colonial_index = None
    milk_index = None
    city_index = None
    victorian_index = None
    jan_index = None
    cat_index = None
    beach_index = None
    
    for i, house in enumerate(houses):
        # Constraint 4: Water drinker is mountain vacation
        if (house['Drink'] == 'water') != (house['Vacation'] == 'mountain'):
            return False
        
        # Constraint 5: Horse owner is Peter
        if house['Animal'] == 'horse' and house['Name'] != 'Peter':
            return False
        
        # Constraint 7: Peter prefers city breaks
        if house['Name'] == 'Peter' and house['Vacation'] != 'city':
            return False
        
        # Constraint 8: Mountain retreat lover has April birthday
        if (house['Vacation'] == 'mountain') != (house['Birthday'] == 'april'):
            return False
        
        # Constraint 9: Eric drinks water
        if house['Name'] == 'Eric' and house['Drink'] != 'water':
            return False
        
        # Collect indices for relative constraints
        if house['HouseStyle'] == 'colonial':
            colonial_index = i
        if house['Drink'] == 'milk':
            milk_index = i
        if house['Vacation'] == 'city':
            city_index = i
        if house['HouseStyle'] == 'victorian':
            victorian_index = i
        if house['Birthday'] == 'jan':
            jan_index = i
        if house['Animal'] == 'cat':
            cat_index = i
        if house['Vacation'] == 'beach':
            beach_index = i
    
    # Constraint 1: Colonial left of milk drinker
    if colonial_index is None or milk_index is None or colonial_index >= milk_index:
        return False
    
    # Constraint 2: City vacation directly left of Victorian house
    if city_index is None or victorian_index is None or victorian_index != city_index + 1:
        return False
    
    # Constraint 3: January birthday directly left of cat owner
    if jan_index is None or cat_index is None or cat_index != jan_index + 1:
        return False
    
    # Constraint 6: Beach vacation left of Victorian house
    if beach_index is None or victorian_index is None or beach_index >= victorian_index:
        return False
    
    return True

def main():
    attributes = {
        'Name': ['Eric', 'Peter', 'Arnold'],
        'Drink': ['milk', 'water', 'tea'],
        'Vacation': ['mountain', 'city', 'beach'],
        'HouseStyle': ['colonial', 'victorian', 'ranch'],
        'Animal': ['cat', 'bird', 'horse'],
        'Birthday': ['jan', 'sept', 'april']
    }
    categories = ['Name', 'Drink', 'Vacation', 'HouseStyle', 'Animal', 'Birthday']
    
    perms = {}
    for cat in categories:
        perms[cat] = list(itertools.permutations(attributes[cat]))
    
    perms_list = [perms[cat] for cat in categories]
    
    found = False
    solution_houses = None
    
    for assignment in itertools.product(*perms_list):
        houses = []
        for i in range(3):
            house = {
                'Name': assignment[0][i],
                'Drink': assignment[1][i],
                'Vacation': assignment[2][i],
                'HouseStyle': assignment[3][i],
                'Animal': assignment[4][i],
                'Birthday': assignment[5][i]
            }
            houses.append(house)
        
        if satisfies(houses):
            found = True
            solution_houses = houses
            break
    
    sol_dict = {
        "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
        "rows": []
    }
    
    if found:
        for i, house in enumerate(solution_houses):
            row = [str(i+1)]
            row.append(house['Name'])
            row.append(house['Drink'])
            row.append(house['Vacation'])
            row.append(house['HouseStyle'])
            row.append(house['Animal'])
            row.append(house['Birthday'])
            sol_dict['rows'].append(row)
    
    output = {'solution': sol_dict}
    print(json.dumps(output))

if __name__ == "__main__":
    main()