import json
from itertools import permutations

def solve():
    # Define all possible values
    names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations = ["cruise", "city", "camping", "beach", "mountain"]
    children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities = ["dane", "norwegian", "brit", "german", "swede"]
    houses = [1, 2, 3, 4, 5]
    
    # Generate all permutations for each attribute
    name_perms = list(permutations(names, 5))
    vac_perms = list(permutations(vacations, 5))
    child_perms = list(permutations(children, 5))
    nat_perms = list(permutations(nationalities, 5))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_assignment in name_perms:
        for vac_assignment in vac_perms:
            for child_assignment in child_perms:
                for nat_assignment in nat_perms:
                    # Build the assignment dictionary
                    assignment = {}
                    for i in range(5):
                        house = i + 1
                        assignment[house] = {
                            'name': name_assignment[i],
                            'vacation': vac_assignment[i],
                            'child': child_assignment[i],
                            'nationality': nat_assignment[i]
                        }
                    
                    # Check all clues
                    # 1. The Norwegian is Peter.
                    norwegian_house = None
                    peter_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'norwegian':
                            norwegian_house = house
                        if assignment[house]['name'] == 'Peter':
                            peter_house = house
                    if norwegian_house != peter_house:
                        continue
                    
                    # 2. The Swedish person is the person's child is named Bella.
                    swedish_house = None
                    bella_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'swede':
                            swedish_house = house
                        if assignment[house]['child'] == 'Bella':
                            bella_house = house
                    if swedish_house != bella_house:
                        continue
                    
                    # 3. The person who loves beach vacations is directly left of the person's child is named Samantha.
                    beach_house = None
                    samantha_house = None
                    for house in houses:
                        if assignment[house]['vacation'] == 'beach':
                            beach_house = house
                        if assignment[house]['child'] == 'Samantha':
                            samantha_house = house
                    if beach_house is None or samantha_house is None:
                        continue
                    if beach_house + 1 != samantha_house:
                        continue
                    
                    # 4. The person's child is named Bella is not in the second house.
                    if bella_house == 2:
                        continue
                    
                    # 5. Alice is the British person.
                    alice_house = None
                    brit_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Alice':
                            alice_house = house
                        if assignment[house]['nationality'] == 'brit':
                            brit_house = house
                    if alice_house != brit_house:
                        continue
                    
                    # 6. The person who likes going on cruises is in the first house.
                    if assignment[1]['vacation'] != 'cruise':
                        continue
                    
                    # 7. The person's child is named Meredith is in the fourth house.
                    if assignment[4]['child'] != 'Meredith':
                        continue
                    
                    # 8. Eric is not in the fifth house.
                    if assignment[5]['name'] == 'Eric':
                        continue
                    
                    # 9. The Swedish person is somewhere to the right of the Norwegian.
                    if swedish_house <= norwegian_house:
                        continue
                    
                    # 10. There is one house between the person's child is named Fred and the person who prefers city breaks.
                    fred_house = None
                    city_house = None
                    for house in houses:
                        if assignment[house]['child'] == 'Fred':
                            fred_house = house
                        if assignment[house]['vacation'] == 'city':
                            city_house = house
                    if fred_house is None or city_house is None:
                        continue
                    if abs(fred_house - city_house) != 2:
                        continue
                    
                    # 11. Bob is the person who enjoys camping trips.
                    bob_house = None
                    camping_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Bob':
                            bob_house = house
                        if assignment[house]['vacation'] == 'camping':
                            camping_house = house
                    if bob_house != camping_house:
                        continue
                    
                    # 12. The Dane is in the fifth house.
                    if assignment[5]['nationality'] != 'dane':
                        continue
                    
                    # 13. The person who enjoys camping trips is not in the fifth house.
                    if camping_house == 5:
                        continue
                    
                    # All constraints satisfied
                    solutions.append(assignment)
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution (should be unique)
    solution = solutions[0]
    
    # Build output
    rows = []
    for house in houses:
        data = solution[house]
        rows.append([
            str(house),
            data['name'],
            data['vacation'],
            data['child'],
            data['nationality']
        ])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, indent=2))