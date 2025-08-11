import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']
    
    # We'll represent each house as a dictionary with the categories as keys
    solution = None
    
    # Generate all possible permutations for each category (this is brute-force and inefficient for larger problems)
    # Instead, we'll use a more efficient constraint satisfaction approach
    
    # Initialize possible values for each house
    from collections import defaultdict
    possible = {
        'house': houses,
        'name': names,
        'car': cars,
        'mother': mothers,
        'hobby': hobbies
    }
    
    # We'll create a list of houses, each with their own possible values
    houses_data = []
    for house in houses:
        houses_data.append({
            'house': house,
            'name': names.copy(),
            'car': cars.copy(),
            'mother': mothers.copy(),
            'hobby': hobbies.copy()
        })
    
    # Apply the clues one by one to narrow down possibilities
    
    # Clue 1: The person who owns a Toyota Camry is in the sixth house.
    for h in houses_data:
        if h['house'] == 6:
            h['car'] = ['toyota camry']
        else:
            if 'toyota camry' in h['car']:
                h['car'].remove('toyota camry')
    
    # Clue 2: Carol is the photography enthusiast.
    for h in houses_data:
        if 'Carol' in h['name']:
            h['hobby'] = ['photography']
        if 'photography' in h['hobby']:
            if 'Carol' not in h['name']:
                h['name'] = [n for n in h['name'] if n != 'Carol'  # Wait, this doesn't make sense
            # Better approach: if hobby is photography, name must be Carol
            if 'photography' in h['hobby']:
                h['name'] = [n for n in h['name'] if n == 'Carol']
    
    # Clue 3: The person who owns a Chevrolet Silverado is the person whose mother's name is Aniya.
    # So for any house, if car is chevrolet silverado, then mother is Aniya, and vice versa
    # We'll note this constraint and apply it during the solving process
    
    # Clue 4: The person who owns a Chevrolet Silverado is not in the second house.
    for h in houses_data:
        if h['house'] == 2:
            if 'chevrolet silverado' in h['car']:
                h['car'].remove('chevrolet silverado')
    
    # Clue 5: The person who owns a Ford F-150 is the person whose mother's name is Sarah.
    # Similar to clue 3, we'll note this constraint
    
    # Clue 6: The person who owns a BMW 3 Series is Bob.
    for h in houses_data:
        if 'bmw 3 series' in h['car']:
            h['name'] = ['Bob']
        if 'Bob' in h['name']:
            h['car'] = [c for c in h['car'] if c == 'bmw 3 series']
    
    # Clue 7: The person whose mother's name is Kailyn is in the sixth house.
    for h in houses_data:
        if h['house'] == 6:
            h['mother'] = ['Kailyn']
        else:
            if 'Kailyn' in h['mother']:
                h['mother'].remove('Kailyn')
    
    # Clue 8: Eric is directly left of the person who enjoys knitting.
    # This means Eric is in house X, knitting is in house X+1
    # So Eric cannot be in house 6, and knitting cannot be in house 1
    
    # Clue 9: There is one house between the person whose mother's name is Sarah and the person who owns a Toyota Camry.
    # Toyota camry is in house 6, so Sarah's mother is in house 4 (since 4 -> 5 -> 6)
    for h in houses_data:
        if h['house'] == 4:
            h['mother'] = ['Sarah']
        else:
            if 'Sarah' in h['mother']:
                h['mother'].remove('Sarah')
    
    # Clue 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    # So knitting is to the left of Penny
    
    # Clue 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    # So honda civic is to the left of Aniya
    
    # Clue 12: Alice is somewhere to the right of the person who owns a Ford F-150.
    # So ford f150 is to the left of Alice
    
    # Clue 13: Eric is the person who enjoys gardening.
    for h in houses_data:
        if 'Eric' in h['name']:
            h['hobby'] = ['gardening']
        if 'gardening' in h['hobby']:
            h['name'] = [n for n in h['name'] if n == 'Eric']
    
    # Clue 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    # So woodworking is to the left of knitting
    
    # Clue 15: There is one house between the person whose mother's name is Sarah and the person who loves cooking.
    # Sarah is in house 4, so cooking is in house 6 (4 -> 5 -> 6)
    for h in houses_data:
        if h['house'] == 6:
            h['hobby'] = ['cooking']
        else:
            if 'cooking' in h['hobby']:
                h['hobby'].remove('cooking')
    
    # Clue 16: The person who owns a Honda Civic is Arnold.
    for h in houses_data:
        if 'honda civic' in h['car']:
            h['name'] = ['Arnold']
        if 'Arnold' in h['name']:
            h['car'] = [c for c in h['car'] if c == 'honda civic']
    
    # Clue 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    # So holly is in X, knitting is in X+1
    
    # Now, let's try to assign based on the constraints
    
    # From clue 13 and 8: Eric is gardening and is directly left of knitting
    # So possible positions for Eric: 1-5, knitting in 2-6
    # But knitting is in X+1 where Eric is in X
    # Also, from clue 17: holly is directly left of knitting, so holly is in Y, knitting in Y+1
    # Therefore, Eric is in Y, holly is in Y, so Eric's mother is holly
    for h in houses_data:
        if 'Eric' in h['name']:
            h['mother'] = ['Holly']
            knitting_house = h['house'] + 1
            # Also, knitting is in h['house'] + 1
            for h2 in houses_data:
                if h2['house'] == knitting_house:
                    h2['hobby'] = ['knitting']
    
    # From clue 14: woodworking is left of knitting
    # So woodworking is in any house < knitting_house
    
    # From clue 10: penny is right of knitting
    # So penny is in any house > knitting_house
    
    # From clue 5: ford f150 is sarah's mother, sarah is in house 4
    for h in houses_data:
        if h['house'] == 4:
            h['mother'] = ['Sarah']
            h['car'] = ['ford f150']
    
    # From clue 12: alice is right of ford f150 (house 4)
    # So alice is in house 5 or 6
    for h in houses_data:
        if h['house'] in [1, 2, 3, 4]:
            if 'Alice' in h['name']:
                h['name'].remove('Alice')
    
    # From clue 3: chevrolet silverado is aniya
    # From clue 11: aniya is right of honda civic
    # honda civic is arnold
    # So find arnold's house (honda civic)
    arnold_house = None
    for h in houses_data:
        if 'Arnold' in h['name']:
            arnold_house = h['house']
            break
    
    if arnold_house is not None:
        # aniya is to the right of arnold
        for h in houses_data:
            if h['house'] <= arnold_house:
                if 'Aniya' in h['mother']:
                    h['mother'].remove('Aniya')
    
    # From clue 7: house 6 mother is kailyn
    # From clue 1: house 6 car is toyota camry
    # From clue 15: house 6 hobby is cooking
    # But from clue 2: carol is photography
    # So if house 6 hobby is cooking, carol is not in house 6
    for h in houses_data:
        if h['house'] == 6:
            h['hobby'] = ['cooking']
            if 'Carol' in h['name']:
                h['name'].remove('Carol')
    
    # From clue 2: carol is photography, so find where photography is
    for h in houses_data:
        if 'photography' in h['hobby']:
            h['name'] = ['Carol']
    
    # From clue 6: bmw is bob
    # So find bob's house
    bob_house = None
    for h in houses_data:
        if 'Bob' in h['name']:
            bob_house = h['house']
            break
    
    if bob_house is not None:
        for h in houses_data:
            if h['house'] == bob_house:
                h['car'] = ['bmw 3 series']
    
    # Now, let's assign based on remaining possibilities
    # We'll use a backtracking approach to try possible assignments
    
    from copy import deepcopy
    
    def backtrack(assignments, index):
        if index == 6:
            return assignments
        current_house = houses_data[index]
        # Try assigning possible values
        for name in current_house['name']:
            if name in [a['name'] for a in assignments if a['name'] is not None]:
                continue
            for car in current_house['car']:
                if car in [a['car'] for a in assignments if a['car'] is not None]:
                    continue
                for mother in current_house['mother']:
                    if mother in [a['mother'] for a in assignments if a['mother'] is not None]:
                        continue
                    for hobby in current_house['hobby']:
                        if hobby in [a['hobby'] for a in assignments if a['hobby'] is not None]:
                            continue
                        # Check constraints
                        # Clue 3: chevrolet silverado <-> aniya
                        if car == 'chevrolet silverado' and mother != 'Aniya':
                            continue
                        if mother == 'Aniya' and car != 'chevrolet silverado':
                            continue
                        # Clue 5: ford f150 <-> sarah
                        if car == 'ford f150' and mother != 'Sarah':
                            continue
                        if mother == 'Sarah' and car != 'ford f150':
                            continue
                        # Clue 8: eric is directly left of knitting
                        if name == 'Eric':
                            knitting_house = None
                            for h in assignments:
                                if h['hobby'] == 'knitting':
                                    knitting_house = h['house']
                            if knitting_house != current_house['house'] + 1:
                                continue
                        # Clue 17: holly is directly left of knitting
                        if mother == 'Holly':
                            knitting_house = None
                            for h in assignments:
                                if h['hobby'] == 'knitting':
                                    knitting_house = h['house']
                            if knitting_house != current_house['house'] + 1:
                                continue
                        # Clue 10: penny is right of knitting
                        if mother == 'Penny':
                            knitting_house = None
                            for h in assignments:
                                if h['hobby'] == 'knitting':
                                    knitting_house = h['house']
                            if knitting_house is None or current_house['house'] <= knitting_house:
                                continue
                        # Clue 11: aniya is right of honda civic
                        if mother == 'Aniya':
                            honda_house = None
                            for h in assignments:
                                if h['car'] == 'honda civic':
                                    honda_house = h['house']
                            if honda_house is None or current_house['house'] <= honda_house:
                                continue
                        # Clue 12: alice is right of ford f150 (house 4)
                        if name == 'Alice' and current_house['house'] <= 4:
                            continue
                        # Clue 14: woodworking is left of knitting
                        if hobby == 'woodworking':
                            knitting_house = None
                            for h in assignments:
                                if h['hobby'] == 'knitting':
                                    knitting_house = h['house']
                            if knitting_house is not None and current_house['house'] >= knitting_house:
                                continue
                        # If all constraints are satisfied, proceed
                        new_assignment = {
                            'house': current_house['house'],
                            'name': name,
                            'car': car,
                            'mother': mother,
                            'hobby': hobby
                        }
                        new_assignments = deepcopy(assignments)
                        new_assignments.append(new_assignment)
                        result = backtrack(new_assignments, index + 1)
                        if result is not None:
                            return result
        return None
    
    initial_assignments = []
    solution = backtrack(initial_assignments, 0)
    
    if solution is None:
        return {"solution": {"header": [], "rows": []}}
    
    # Format the solution as required
    header = ["House", "Name", "car", "mother", "hobby"]
    rows = []
    for house in sorted(solution, key=lambda x: x['house']):
        rows.append([
            str(house['house']),
            house['name'],
            house['car'],
            house['mother'],
            house['hobby']
        ])
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))