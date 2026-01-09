import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-4)
    houses = [1, 2, 3, 4]
    
    # Define domains for each attribute
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'smoothie_{house}', smoothies)
        problem.addVariable(f'cigar_{house}', cigars)
        problem.addVariable(f'height_{house}', heights)
        problem.addVariable(f'phone_{house}', phones)
    
    # All attributes must be different across houses
    problem.addConstraint(AllDifferentConstraint(), [f'name_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'smoothie_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'cigar_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'height_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'phone_{h}' for h in houses])
    
    # Clue 1: The Dragonfruit smoothie lover is Eric.
    for house in houses:
        problem.addConstraint(
            lambda smoothie, name: not (smoothie == 'dragonfruit') or (name == 'Eric'),
            [f'smoothie_{house}', f'name_{house}']
        )
        problem.addConstraint(
            lambda smoothie, name: not (name == 'Eric') or (smoothie == 'dragonfruit'),
            [f'smoothie_{house}', f'name_{house}']
        )
    
    # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
    for house in houses:
        problem.addConstraint(
            lambda cigar, smoothie: not (cigar == 'dunhill') or (smoothie == 'cherry'),
            [f'cigar_{house}', f'smoothie_{house}']
        )
        problem.addConstraint(
            lambda cigar, smoothie: not (smoothie == 'cherry') or (cigar == 'dunhill'),
            [f'cigar_{house}', f'smoothie_{house}']
        )
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    for i in range(1, 4):
        problem.addConstraint(
            lambda phone1, phone2: not (phone1 == 'samsung galaxy s21') or (phone2 == 'iphone 13'),
            [f'phone_{i}', f'phone_{i+1}']
        )
    
    # Clue 4: The Dunhill smoker is somewhere to the right of the person who is very short.
    for i in range(1, 5):
        for j in range(1, 5):
            if i <= j:
                continue
            problem.addConstraint(
                lambda cigar_i, height_j, house_i=i, house_j=j: 
                    not (cigar_i == 'dunhill' and height_j == 'very short') or (house_i > house_j),
                [f'cigar_{i}', f'height_{j}']
            )
    
    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    for i in range(1, 5):
        for j in range(1, 5):
            if i <= j:
                continue
            problem.addConstraint(
                lambda smoothie_i, smoothie_j, house_i=i, house_j=j: 
                    not (smoothie_i == 'watermelon' and smoothie_j == 'desert') or (house_i > house_j),
                [f'smoothie_{i}', f'smoothie_{j}']
            )
    
    # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
    for house in houses:
        problem.addConstraint(
            lambda cigar, phone: not (cigar == 'prince') or (phone == 'oneplus 9'),
            [f'cigar_{house}', f'phone_{house}']
        )
        problem.addConstraint(
            lambda cigar, phone: not (phone == 'oneplus 9') or (cigar == 'prince'),
            [f'cigar_{house}', f'phone_{house}']
        )
    
    # Clue 7: The person who is tall is in the third house.
    problem.addConstraint(lambda height: height == 'tall', ['height_3'])
    
    # Clue 8: The person who is very short is the person who uses an iPhone 13.
    for house in houses:
        problem.addConstraint(
            lambda height, phone: not (height == 'very short') or (phone == 'iphone 13'),
            [f'height_{house}', f'phone_{house}']
        )
        problem.addConstraint(
            lambda height, phone: not (phone == 'iphone 13') or (height == 'very short'),
            [f'height_{house}', f'phone_{house}']
        )
    
    # Clue 9: The person who smokes Blue Master is not in the first house.
    problem.addConstraint(lambda cigar: cigar != 'blue master', ['cigar_1'])
    
    # Clue 10: The Dunhill smoker is the person who is short.
    for house in houses:
        problem.addConstraint(
            lambda cigar, height: not (cigar == 'dunhill') or (height == 'short'),
            [f'cigar_{house}', f'height_{house}']
        )
        problem.addConstraint(
            lambda cigar, height: not (height == 'short') or (cigar == 'dunhill'),
            [f'cigar_{house}', f'height_{house}']
        )
    
    # Clue 11: Peter is not in the third house.
    problem.addConstraint(lambda name: name != 'Peter', ['name_3'])
    
    # Clue 12: Arnold is the person who uses a Google Pixel 6.
    for house in houses:
        problem.addConstraint(
            lambda name, phone: not (name == 'Arnold') or (phone == 'google pixel 6'),
            [f'name_{house}', f'phone_{house}']
        )
        problem.addConstraint(
            lambda name, phone: not (phone == 'google pixel 6') or (name == 'Arnold'),
            [f'name_{house}', f'phone_{house}']
        )
    
    # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
    for house in houses:
        problem.addConstraint(
            lambda smoothie, cigar: not (smoothie == 'dragonfruit') or (cigar == 'pall mall'),
            [f'smoothie_{house}', f'cigar_{house}']
        )
        problem.addConstraint(
            lambda smoothie, cigar: not (cigar == 'pall mall') or (smoothie == 'dragonfruit'),
            [f'smoothie_{house}', f'cigar_{house}']
        )
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build result
    header = ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'smoothie_{house}'],
            solution[f'cigar_{house}'],
            solution[f'height_{house}'],
            solution[f'phone_{house}']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))