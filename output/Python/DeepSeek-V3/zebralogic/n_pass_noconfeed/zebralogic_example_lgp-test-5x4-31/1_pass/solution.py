import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    vacation_perms = list(permutations(vacations))
    children_perms = list(permutations(children))
    nationality_perms = list(permutations(nationalities))
    
    # Try all combinations until we find one that satisfies all constraints
    for name_assignment in name_perms:
        for vacation_assignment in vacation_perms:
            for children_assignment in children_perms:
                for nationality_assignment in nationality_perms:
                    # Create assignment dictionaries for each house
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'name': name_assignment[i],
                            'vacation': vacation_assignment[i],
                            'children': children_assignment[i],
                            'nationality': nationality_assignment[i]
                        }
                    
                    # Check all constraints
                    # Constraint 1: The Norwegian is Peter
                    norwegian_house = None
                    peter_house = None
                    for house, attrs in assignment.items():
                        if attrs['nationality'] == 'norwegian':
                            norwegian_house = house
                        if attrs['name'] == 'Peter':
                            peter_house = house
                    if norwegian_house != peter_house:
                        continue
                    
                    # Constraint 2: The Swedish person is the person's child is named Bella
                    swede_house = None
                    bella_house = None
                    for house, attrs in assignment.items():
                        if attrs['nationality'] == 'swede':
                            swede_house = house
                        if attrs['children'] == 'Bella':
                            bella_house = house
                    if swede_house != bella_house:
                        continue
                    
                    # Constraint 3: The person who loves beach vacations is directly left of the person's child is named Samantha
                    beach_house = None
                    samantha_house = None
                    for house, attrs in assignment.items():
                        if attrs['vacation'] == 'beach':
                            beach_house = house
                        if attrs['children'] == 'Samantha':
                            samantha_house = house
                    if beach_house is None or samantha_house is None or beach_house + 1 != samantha_house:
                        continue
                    
                    # Constraint 4: The person's child is named Bella is not in the second house
                    if bella_house == 2:
                        continue
                    
                    # Constraint 5: Alice is the British person
                    alice_house = None
                    brit_house = None
                    for house, attrs in assignment.items():
                        if attrs['name'] == 'Alice':
                            alice_house = house
                        if attrs['nationality'] == 'brit':
                            brit_house = house
                    if alice_house != brit_house:
                        continue
                    
                    # Constraint 6: The person who likes going on cruises is in the first house
                    if assignment[1]['vacation'] != 'cruise':
                        continue
                    
                    # Constraint 7: The person's child is named Meredith is in the fourth house
                    if assignment[4]['children'] != 'Meredith':
                        continue
                    
                    # Constraint 8: Eric is not in the fifth house
                    if assignment[5]['name'] == 'Eric':
                        continue
                    
                    # Constraint 9: The Swedish person is somewhere to the right of the Norwegian
                    if swede_house <= norwegian_house:
                        continue
                    
                    # Constraint 10: There is one house between the person's child is named Fred and the person who prefers city breaks
                    fred_house = None
                    city_house = None
                    for house, attrs in assignment.items():
                        if attrs['children'] == 'Fred':
                            fred_house = house
                        if attrs['vacation'] == 'city':
                            city_house = house
                    if fred_house is None or city_house is None or abs(fred_house - city_house) != 2:
                        continue
                    
                    # Constraint 11: Bob is the person who enjoys camping trips
                    bob_house = None
                    camping_house = None
                    for house, attrs in assignment.items():
                        if attrs['name'] == 'Bob':
                            bob_house = house
                        if attrs['vacation'] == 'camping':
                            camping_house = house
                    if bob_house != camping_house:
                        continue
                    
                    # Constraint 12: The Dane is in the fifth house
                    if assignment[5]['nationality'] != 'dane':
                        continue
                    
                    # Constraint 13: The person who enjoys camping trips is not in the fifth house
                    if camping_house == 5:
                        continue
                    
                    # If we reach here, all constraints are satisfied
                    # Format the solution as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        attrs = assignment[house]
                        solution["solution"]["rows"].append([
                            str(house),
                            attrs['name'],
                            attrs['vacation'],
                            attrs['children'],
                            attrs['nationality']
                        ])
                    
                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()