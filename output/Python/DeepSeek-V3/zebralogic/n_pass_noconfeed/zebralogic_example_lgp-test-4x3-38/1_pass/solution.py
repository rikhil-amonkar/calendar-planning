import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    mother_perms = list(permutations(mothers))
    flower_perms = list(permutations(flowers))
    
    # Try all combinations to find the one that satisfies all constraints
    for name_assignment in name_perms:
        for mother_assignment in mother_perms:
            for flower_assignment in flower_perms:
                # Create assignment dictionaries for easy lookup
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'name': name_assignment[i],
                        'mother': mother_assignment[i],
                        'flower': flower_assignment[i]
                    }
                
                # Check all constraints
                # Constraint 8: Alice is in the third house
                if assignment[3]['name'] != 'Alice':
                    continue
                
                # Constraint 1: Alice is The person whose mother's name is Kailyn
                alice_house = None
                kailyn_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Alice':
                        alice_house = house
                    if assignment[house]['mother'] == 'Kailyn':
                        kailyn_house = house
                if alice_house != kailyn_house:
                    continue
                
                # Constraint 2: The person whose mother's name is Janelle is somewhere to the right of Arnold
                janelle_house = None
                arnold_house = None
                for house in houses:
                    if assignment[house]['mother'] == 'Janelle':
                        janelle_house = house
                    if assignment[house]['name'] == 'Arnold':
                        arnold_house = house
                if janelle_house is None or arnold_house is None or janelle_house <= arnold_house:
                    continue
                
                # Constraint 3: Peter is somewhere to the right of the person who loves a carnations arrangement
                peter_house = None
                carnations_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Peter':
                        peter_house = house
                    if assignment[house]['flower'] == 'carnations':
                        carnations_house = house
                if peter_house is None or carnations_house is None or peter_house <= carnations_house:
                    continue
                
                # Constraint 4: Eric is the person who loves a bouquet of daffodils
                eric_house = None
                daffodils_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Eric':
                        eric_house = house
                    if assignment[house]['flower'] == 'daffodils':
                        daffodils_house = house
                if eric_house != daffodils_house:
                    continue
                
                # Constraint 5: Arnold is The person whose mother's name is Holly
                arnold_house = None
                holly_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Arnold':
                        arnold_house = house
                    if assignment[house]['mother'] == 'Holly':
                        holly_house = house
                if arnold_house != holly_house:
                    continue
                
                # Constraint 6: The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly
                if carnations_house is None or holly_house is None or carnations_house <= holly_house:
                    continue
                
                # Constraint 7: The person who loves the bouquet of lilies is directly left of Alice
                lilies_house = None
                for house in houses:
                    if assignment[house]['flower'] == 'lilies':
                        lilies_house = house
                if lilies_house is None or lilies_house + 1 != alice_house:
                    continue
                
                # If we reach here, all constraints are satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Flower"],
                        "rows": []
                    }
                }
                
                for house in houses:
                    row = [
                        str(house),
                        assignment[house]['name'],
                        assignment[house]['mother'],
                        assignment[house]['flower']
                    ]
                    solution["solution"]["rows"].append(row)
                
                print(json.dumps(solution, indent=2))
                return
    
    print('{"solution": {"header": ["House", "Name", "Mother", "Flower"], "rows": []}}')

if __name__ == "__main__":
    main()