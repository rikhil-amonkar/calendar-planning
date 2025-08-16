from z3 import *

def solve_housing_puzzle():
    # Initialize the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the attributes
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

    # Create variables for each attribute in each house
    name = {h: String(f'name_{h}') for h in houses}
    smoothie = {h: String(f'smoothie_{h}') for h in houses}
    cigar = {h: String(f'cigar_{h}') for h in houses}
    height = {h: String(f'height_{h}') for h in houses}
    phone = {h: String(f'phone_{h}') for h in houses}

    # Add constraints that each attribute is one of the possible values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([smoothie[h] == sm for sm in smoothies]))
        s.add(Or([cigar[h] == cg for cg in cigars]))
        s.add(Or([height[h] == ht for ht in heights]))
        s.add(Or([phone[h] == ph for ph in phones]))

    # Add uniqueness constraints for each attribute across houses
    for attr in [name, smoothie, cigar, height, phone]:
        for h1 in houses:
            for h2 in houses:
                if h1 < h2:
                    s.add(attr[h1] != attr[h2])

    # Add clues
    # Clue 1: The Dragonfruit smoothie lover is Eric.
    for h in houses:
        s.add(Implies(smoothie[h] == 'dragonfruit', name[h] == 'Eric'))

    # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
    for h in houses:
        s.add(Implies(cigar[h] == 'dunhill', smoothie[h] == 'cherry'))

    # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    for h in range(1, 4):
        s.add(Implies(phone[h] == 'samsung galaxy s21', phone[h+1] == 'iphone 13'))

    # Clue 4: The Dunhill smoker is somewhere to the right of the person who is very short.
    for h_dunhill in houses:
        for h_very_short in houses:
            if h_dunhill > h_very_short:
                s.add(Implies(And(cigar[h_dunhill] == 'dunhill', height[h_very_short] == 'very short'), True))
            else:
                s.add(Implies(And(cigar[h_dunhill] == 'dunhill', height[h_very_short] == 'very short'), False))

    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    for h_desert in houses:
        for h_watermelon in houses:
            if h_watermelon > h_desert:
                s.add(Implies(And(smoothie[h_desert] == 'desert', smoothie[h_watermelon] == 'watermelon'), True))
            else:
                s.add(Implies(And(smoothie[h_desert] == 'desert', smoothie[h_watermelon] == 'watermelon'), False))

    # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
    for h in houses:
        s.add(Implies(cigar[h] == 'prince', phone[h] == 'oneplus 9'))

    # Clue 7: The person who is tall is in the third house.
    s.add(height[3] == 'tall')

    # Clue 8: The person who is very short is the person who uses an iPhone 13.
    for h in houses:
        s.add(Implies(height[h] == 'very short', phone[h] == 'iphone 13'))

    # Clue 9: The person who smokes Blue Master is not in the first house.
    s.add(cigar[1] != 'blue master')

    # Clue 10: The Dunhill smoker is the person who is short.
    for h in houses:
        s.add(Implies(cigar[h] == 'dunhill', height[h] == 'short'))

    # Clue 11: Peter is not in the third house.
    s.add(name[3] != 'Peter')

    # Clue 12: Arnold is the person who uses a Google Pixel 6.
    for h in houses:
        s.add(Implies(name[h] == 'Arnold', phone[h] == 'google pixel 6'))

    # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
    for h in houses:
        s.add(Implies(smoothie[h] == 'dragonfruit', cigar[h] == 'pall mall'))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                "rows": []
            }
        }
        for h in houses:
            row = [
                str(h),
                str(m.evaluate(name[h])),
                str(m.evaluate(smoothie[h])),
                str(m.evaluate(cigar[h])),
                str(m.evaluate(height[h])),
                str(m.evaluate(phone[h]))
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": [], "rows": []}}

# Print the solution in JSON format
import json
print(json.dumps(solve_housing_puzzle(), indent=2))