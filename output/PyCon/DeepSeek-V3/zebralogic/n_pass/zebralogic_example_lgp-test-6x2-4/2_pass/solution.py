import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phones = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']
    
    # Add variables for names and phones
    problem.addVariables(['name_' + str(h) for h in houses], names)
    problem.addVariables(['phone_' + str(h) for h in houses], phones)
    
    # All names and phones must be different
    problem.addConstraint(AllDifferentConstraint(), ['name_' + str(h) for h in houses])
    problem.addConstraint(AllDifferentConstraint(), ['phone_' + str(h) for h in houses])
    
    # Clue 1: The person who uses an iPhone 13 is Alice.
    for h in houses:
        problem.addConstraint(
            lambda name, phone, h=h: not (phone == 'iphone 13') or name == 'Alice',
            ['name_' + str(h), 'phone_' + str(h)]
        )
    
    # Clue 2: The person who uses a Huawei P50 is in the first house.
    problem.addConstraint(lambda phone: phone == 'huawei p50', ['phone_1'])
    
    # Clue 3: The person who uses a OnePlus 9 is in the sixth house.
    problem.addConstraint(lambda phone: phone == 'oneplus 9', ['phone_6'])
    
    # Clue 4: The person who uses a Google Pixel 6 is not in the second house.
    problem.addConstraint(lambda phone: phone != 'google pixel 6', ['phone_2'])
    
    # Clue 5: The person who uses an iPhone 13 is not in the second house.
    problem.addConstraint(lambda phone: phone != 'iphone 13', ['phone_2'])
    
    # Clue 6: There is one house between Bob and Carol.
    # This means |position_Bob - position_Carol| = 2
    bob_carol_pairs = []
    for h1 in houses:
        for h2 in houses:
            if abs(h1 - h2) == 2:
                bob_carol_pairs.append((h1, h2))
    
    def bob_carol_constraint(*all_names):
        # Check if Bob and Carol are in positions that differ by 2
        name_vars = ['name_' + str(h) for h in houses]
        name_dict = dict(zip(name_vars, all_names))
        
        bob_house = None
        carol_house = None
        for h in houses:
            if name_dict['name_' + str(h)] == 'Bob':
                bob_house = h
            if name_dict['name_' + str(h)] == 'Carol':
                carol_house = h
        
        return bob_house is not None and carol_house is not None and abs(bob_house - carol_house) == 2
    
    problem.addConstraint(bob_carol_constraint, ['name_' + str(h) for h in houses])
    
    # Clue 7: The person who uses a Huawei P50 is Eric.
    for h in houses:
        problem.addConstraint(
            lambda name, phone, h=h: not (phone == 'huawei p50') or name == 'Eric',
            ['name_' + str(h), 'phone_' + str(h)]
        )
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is in the third house.
    problem.addConstraint(lambda phone: phone == 'xiaomi mi 11', ['phone_3'])
    
    # Clue 9: Alice is somewhere to the left of Carol.
    def alice_left_of_carol(*all_names):
        name_vars = ['name_' + str(h) for h in houses]
        name_dict = dict(zip(name_vars, all_names))
        
        alice_house = None
        carol_house = None
        for h in houses:
            if name_dict['name_' + str(h)] == 'Alice':
                alice_house = h
            if name_dict['name_' + str(h)] == 'Carol':
                carol_house = h
        
        return alice_house is not None and carol_house is not None and alice_house < carol_house
    
    problem.addConstraint(alice_left_of_carol, ['name_' + str(h) for h in houses])
    
    # Clue 10: Arnold is the person who uses a OnePlus 9.
    for h in houses:
        problem.addConstraint(
            lambda name, phone, h=h: not (phone == 'oneplus 9') or name == 'Arnold',
            ['name_' + str(h), 'phone_' + str(h)]
        )
    
    # Find solution
    solutions = problem.getSolutions()
    if not solutions:
        return None
    
    solution = solutions[0]
    
    # Build output structure
    result = {
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": []
        }
    }
    
    for house in sorted(houses):
        name_key = 'name_' + str(house)
        phone_key = 'phone_' + str(house)
        result["solution"]["rows"].append([str(house), solution[name_key], solution[phone_key]])
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))