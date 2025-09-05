import itertools
import json

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['milk', 'water', 'tea']
    vacations = ['mountain', 'city', 'beach']
    styles = ['colonial', 'victorian', 'ranch']
    animals = ['cat', 'bird', 'horse']
    birthdays = ['jan', 'sept', 'april']
    
    # Generate all permutations for each attribute
    names_perms = list(itertools.permutations(names))
    drinks_perms = list(itertools.permutations(drinks))
    vacations_perms = list(itertools.permutations(vacations))
    styles_perms = list(itertools.permutations(styles))
    animals_perms = list(itertools.permutations(animals))
    birthdays_perms = list(itertools.permutations(birthdays))
    
    # Iterate over all combinations of permutations
    for n in names_perms:
        for d in drinks_perms:
            for v in vacations_perms:
                for s in styles_perms:
                    for a in animals_perms:
                        for b in birthdays_perms:
                            # Check constraints
                            # Constraint 4: water drinker == mountain vacation
                            water_mountain_ok = True
                            for i in range(3):
                                if (d[i] == 'water' and v[i] != 'mountain') or (v[i] == 'mountain' and d[i] != 'water'):
                                    water_mountain_ok = False
                                    break
                            if not water_mountain_ok:
                                continue
                                
                            # Constraint 5: horse animal == Peter
                            horse_peter_ok = True
                            for i in range(3):
                                if (a[i] == 'horse' and n[i] != 'Peter') or (n[i] == 'Peter' and a[i] != 'horse'):
                                    horse_peter_ok = False
                                    break
                            if not horse_peter_ok:
                                continue
                                
                            # Constraint 7: Peter == city vacation
                            peter_city_ok = True
                            for i in range(3):
                                if (n[i] == 'Peter' and v[i] != 'city') or (v[i] == 'city' and n[i] != 'Peter'):
                                    peter_city_ok = False
                                    break
                            if not peter_city_ok:
                                continue
                                
                            # Constraint 8: mountain vacation == april birthday
                            mountain_april_ok = True
                            for i in range(3):
                                if (v[i] == 'mountain' and b[i] != 'april') or (b[i] == 'april' and v[i] != 'mountain'):
                                    mountain_april_ok = False
                                    break
                            if not mountain_april_ok:
                                continue
                                
                            # Constraint 9: Eric == water drinker
                            eric_water_ok = True
                            for i in range(3):
                                if (n[i] == 'Eric' and d[i] != 'water') or (d[i] == 'water' and n[i] != 'Eric'):
                                    eric_water_ok = False
                                    break
                            if not eric_water_ok:
                                continue
                                
                            # Constraint 1: colonial left of milk
                            colonial_house = None
                            milk_house = None
                            for i in range(3):
                                if s[i] == 'colonial':
                                    colonial_house = i
                                if d[i] == 'milk':
                                    milk_house = i
                            if colonial_house is None or milk_house is None or colonial_house >= milk_house:
                                continue
                                
                            # Constraint 2: city directly left of victorian
                            city_house = None
                            victorian_house = None
                            for i in range(3):
                                if v[i] == 'city':
                                    city_house = i
                                if s[i] == 'victorian':
                                    victorian_house = i
                            if city_house is None or victorian_house is None or city_house + 1 != victorian_house:
                                continue
                                
                            # Constraint 3: jan directly left of cat
                            jan_house = None
                            cat_house = None
                            for i in range(3):
                                if b[i] == 'jan':
                                    jan_house = i
                                if a[i] == 'cat':
                                    cat_house = i
                            if jan_house is None or cat_house is None or jan_house + 1 != cat_house:
                                continue
                                
                            # Constraint 6: victorian right of beach
                            beach_house = None
                            for i in range(3):
                                if v[i] == 'beach':
                                    beach_house = i
                            if victorian_house is None or beach_house is None or victorian_house <= beach_house:
                                continue
                                
                            # All constraints satisfied, build the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                                    "rows": [
                                        ["1", n[0], d[0], v[0], s[0], a[0], b[0]],
                                        ["2", n[1], d[1], v[1], s[1], a[1], b[1]],
                                        ["3", n[2], d[2], v[2], s[2], a[2], b[2]]
                                    ]
                                }
                            }
                            
                            # Output the solution as JSON
                            print(json.dumps(solution))
                            return
                            
    print("No solution found")

if __name__ == "__main__":
    main()