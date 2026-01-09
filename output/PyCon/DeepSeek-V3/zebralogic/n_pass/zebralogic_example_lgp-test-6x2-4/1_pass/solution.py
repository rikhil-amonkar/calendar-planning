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
            lambda name, phone: not (phone == 'iphone 13') or name == 'Alice',
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
    for h1 in houses:
        for h2 in houses:
            if abs(h1 - h2) == 2:
                problem.addConstraint(
                    lambda name1, name2: (name1 == 'Bob' and name2 == 'Carol') or 
                                         (name1 == 'Carol' and name2 == 'Bob'),
                    ['name_' + str(h1), 'name_' + str(h2)]
                )
    
    # Clue 7: The person who uses a Huawei P50 is Eric.
    for h in houses:
        problem.addConstraint(
            lambda name, phone: not (phone == 'huawei p50') or name == 'Eric',
            ['name_' + str(h), 'phone_' + str(h)]
        )
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is in the third house.
    problem.addConstraint(lambda phone: phone == 'xiaomi mi 11', ['phone_3'])
    
    # Clue 9: Alice is somewhere to the left of Carol.
    for h_alice in houses:
        for h_carol in houses:
            if h_alice >= h_carol:
                problem.addConstraint(
                    lambda name1, name2: not (name1 == 'Alice' and name2 == 'Carol'),
                    ['name_' + str(h_alice), 'name_' + str(h_carol)]
                )
    
    # Clue 10: Arnold is the person who uses a OnePlus 9.
    for h in houses:
        problem.addConstraint(
            lambda name, phone: not (phone == 'oneplus 9') or name == 'Arnold',
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