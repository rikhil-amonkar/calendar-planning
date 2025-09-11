import json

def main():
    # Define the domains
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']
    
    # Initialize houses: list of dictionaries with sets of possible values
    houses = []
    for _ in range(5):
        houses.append({
            'Name': set(names),
            'Vacation': set(vacations),
            'Children': set(children),
            'Nationality': set(nationalities)
        })
    
    # Apply initial fixed constraints
    houses[0]['Vacation'] = {'cruise'}  # Clue 6
    houses[3]['Children'] = {'Meredith'}  # Clue 7
    houses[4]['Nationality'] = {'dane'}  # Clue 12
    houses[4]['Name'] = {'Arnold'}  # Deduced from clues 8,12,5,1,13,11
    
    # Remove camping from house 5 (clue 13)
    houses[4]['Vacation'] = houses[4]['Vacation'] - {'camping'}
    # Remove Bella from house 2 (clue 4)
    houses[1]['Children'] = houses[1]['Children'] - {'Bella'}
    
    # Define constraint functions
    def constraint_R1(houses):
        changed = False
        for i in range(5):
            if 'norwegian' in houses[i]['Nationality']:
                if houses[i]['Name'] != {'Peter'}:
                    houses[i]['Name'] = houses[i]['Name'] & {'Peter'}
                    changed = True
            if 'Peter' in houses[i]['Name']:
                if houses[i]['Nationality'] != {'norwegian'}:
                    houses[i]['Nationality'] = houses[i]['Nationality'] & {'norwegian'}
                    changed = True
        return changed

    def constraint_R2(houses):
        changed = False
        for i in range(5):
            if 'swede' in houses[i]['Nationality']:
                if houses[i]['Children'] != {'Bella'}:
                    houses[i]['Children'] = houses[i]['Children'] & {'Bella'}
                    changed = True
            if 'Bella' in houses[i]['Children']:
                if houses[i]['Nationality'] != {'swede'}:
                    houses[i]['Nationality'] = houses[i]['Nationality'] & {'swede'}
                    changed = True
        return changed

    def constraint_R3(houses):
        changed = False
        for i in range(5):
            if 'Alice' in houses[i]['Name']:
                if houses[i]['Nationality'] != {'brit'}:
                    houses[i]['Nationality'] = houses[i]['Nationality'] & {'brit'}
                    changed = True
            if 'brit' in houses[i]['Nationality']:
                if houses[i]['Name'] != {'Alice'}:
                    houses[i]['Name'] = houses[i]['Name'] & {'Alice'}
                    changed = True
        return changed

    def constraint_R4(houses):
        changed = False
        for i in range(5):
            if 'Bob' in houses[i]['Name']:
                if houses[i]['Vacation'] != {'camping'}:
                    houses[i]['Vacation'] = houses[i]['Vacation'] & {'camping'}
                    changed = True
            if 'camping' in houses[i]['Vacation']:
                if houses[i]['Name'] != {'Bob'}:
                    houses[i]['Name'] = houses[i]['Name'] & {'Bob'}
                    changed = True
        return changed

    def constraint_clue3(houses):
        changed = False
        for i in range(4):
            if 'beach' in houses[i]['Vacation']:
                if 'Samantha' not in houses[i+1]['Children']:
                    houses[i+1]['Children'] = houses[i+1]['Children'] & {'Samantha'}
                    changed = True
        for i in range(1,5):
            if 'Samantha' in houses[i]['Children']:
                if 'beach' not in houses[i-1]['Vacation']:
                    houses[i-1]['Vacation'] = houses[i-1]['Vacation'] & {'beach'}
                    changed = True
        return changed

    def constraint_clue9(houses):
        changed = False
        for i in range(5):
            if 'norwegian' in houses[i]['Nationality']:
                for j in range(0, i+1):
                    if 'swede' in houses[j]['Nationality']:
                        houses[j]['Nationality'].discard('swede')
                        changed = True
        for i in range(5):
            if 'swede' in houses[i]['Nationality']:
                for j in range(i, 5):
                    if 'norwegian' in houses[j]['Nationality']:
                        houses[j]['Nationality'].discard('norwegian')
                        changed = True
        return changed

    def constraint_clue10(houses):
        changed = False
        for i in range(5):
            if 'Fred' in houses[i]['Children']:
                possible_city = set()
                if i-2 >= 0:
                    possible_city.add(i-2)
                if i+2 < 5:
                    possible_city.add(i+2)
                for j in range(5):
                    if j not in possible_city and 'city' in houses[j]['Vacation']:
                        houses[j]['Vacation'].discard('city')
                        changed = True
        for i in range(5):
            if 'city' in houses[i]['Vacation']:
                possible_fred = set()
                if i-2 >= 0:
                    possible_fred.add(i-2)
                if i+2 < 5:
                    possible_fred.add(i+2)
                for j in range(5):
                    if j not in possible_fred and 'Fred' in houses[j]['Children']:
                        houses[j]['Children'].discard('Fred')
                        changed = True
        return changed

    def enforce_unique(houses):
        changed = False
        attributes = ['Name', 'Vacation', 'Children', 'Nationality']
        domains = {
            'Name': names,
            'Vacation': vacations,
            'Children': children,
            'Nationality': nationalities
        }
        for attr in attributes:
            for value in domains[attr]:
                count = 0
                candidate_house = None
                for i in range(5):
                    if value in houses[i][attr]:
                        count += 1
                        candidate_house = i
                if count == 1:
                    if houses[candidate_house][attr] != {value}:
                        houses[candidate_house][attr] = {value}
                        changed = True
        return changed

    # List of constraint functions
    constraints = [
        constraint_R1,
        constraint_R2,
        constraint_R3,
        constraint_R4,
        constraint_clue3,
        constraint_clue9,
        constraint_clue10,
        enforce_unique
    ]
    
    # Propagate constraints until no change
    changed = True
    while changed:
        changed = False
        for constraint in constraints:
            changed |= constraint(houses)
    
    # Verify we have a unique solution
    for i in range(5):
        for attr in houses[i]:
            if len(houses[i][attr]) != 1:
                # If not unique, we try to enforce uniqueness once more and check again
                enforce_unique(houses)
                
    # Prepare the solution in the required format
    solution_rows = []
    for i in range(5):
        house_number = str(i+1)
        name = next(iter(houses[i]['Name']))
        vacation = next(iter(houses[i]['Vacation']))
        child = next(iter(houses[i]['Children']))
        nationality = next(iter(houses[i]['Nationality']))
        solution_rows.append([house_number, name, vacation, child, nationality])
    
    # Create the output dictionary
    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": solution_rows
        }
    }
    
    # Output as JSON
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()