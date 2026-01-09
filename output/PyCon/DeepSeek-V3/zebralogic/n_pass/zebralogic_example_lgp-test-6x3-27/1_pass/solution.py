import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    car_models = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'occupation_{house}', occupations)
        problem.addVariable(f'car_{house}', car_models)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f'name_{house}' for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'occupation_{house}' for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'car_{house}' for house in houses])
    
    # Clue 1: The person who owns a Ford F-150 is in the fifth house.
    problem.addConstraint(lambda car: car == 'ford f150', ['car_5'])
    
    # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
    problem.addConstraint(lambda car: car != 'chevrolet silverado', ['car_2'])
    
    # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
    for house in houses:
        if house > 1:
            problem.addConstraint(
                lambda car_left, name_left, car_right, name_right: 
                not (car_left == 'honda civic' and name_right == 'Peter') and
                not (car_right == 'honda civic' and name_left == 'Peter'),
                [f'car_{house-1}', f'name_{house-1}', f'car_{house}', f'name_{house}']
            )
    
    # Clue 4: The person who is a lawyer is not in the fifth house.
    problem.addConstraint(lambda occupation: occupation != 'lawyer', ['occupation_5'])
    
    # Clue 5: The person who is a nurse is directly left of the person who is an artist.
    for house in range(1, 6):
        problem.addConstraint(
            lambda occ_left, occ_right: not (occ_left == 'nurse' and occ_right != 'artist'),
            [f'occupation_{house}', f'occupation_{house+1}']
        )
    
    # Clue 6: Carol is somewhere to the right of Eric.
    for eric_house in houses:
        for carol_house in houses:
            if carol_house <= eric_house:
                problem.addConstraint(
                    lambda name1, name2, e_house=eric_house, c_house=carol_house: 
                    not (name1 == 'Eric' and name2 == 'Carol' and c_house <= e_house),
                    [f'name_{eric_house}', f'name_{carol_house}']
                )
    
    # Clue 7: The person who is a doctor is Eric.
    for house in houses:
        problem.addConstraint(
            lambda name, occupation: not (name == 'Eric' and occupation != 'doctor') and
                                   not (occupation == 'doctor' and name != 'Eric'),
            [f'name_{house}', f'occupation_{house}']
        )
    
    # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
    for teacher_house in houses:
        for nurse_house in houses:
            if nurse_house <= teacher_house:
                problem.addConstraint(
                    lambda occ1, occ2, t_house=teacher_house, n_house=nurse_house: 
                    not (occ1 == 'teacher' and occ2 == 'nurse' and n_house <= t_house),
                    [f'occupation_{teacher_house}', f'occupation_{nurse_house}']
                )
    
    # Clue 9: Carol is not in the sixth house.
    problem.addConstraint(lambda name: name != 'Carol', ['name_6'])
    
    # Clue 10: The person who is an engineer is Bob.
    for house in houses:
        problem.addConstraint(
            lambda name, occupation: not (name == 'Bob' and occupation != 'engineer') and
                                   not (occupation == 'engineer' and name != 'Bob'),
            [f'name_{house}', f'occupation_{house}']
        )
    
    # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
    for house in houses:
        problem.addConstraint(
            lambda car, occupation: not (car == 'toyota camry' and occupation != 'nurse') and
                                  not (occupation == 'nurse' and car != 'toyota camry'),
            [f'car_{house}', f'occupation_{house}']
        )
    
    # Clue 12: There is one house between Peter and the person who is a lawyer.
    for peter_house in houses:
        for lawyer_house in houses:
            if abs(peter_house - lawyer_house) != 2:
                problem.addConstraint(
                    lambda name, occupation, p_house=peter_house, l_house=lawyer_house: 
                    not (name == 'Peter' and occupation == 'lawyer'),
                    [f'name_{p_house}', f'occupation_{l_house}']
                )
    
    # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
    for tesla_house in houses:
        for bob_house in houses:
            if abs(tesla_house - bob_house) != 2:
                problem.addConstraint(
                    lambda car, name, t_house=tesla_house, b_house=bob_house: 
                    not (car == 'tesla model 3' and name == 'Bob'),
                    [f'car_{t_house}', f'name_{b_house}']
                )
    
    # Clue 14: Arnold is the person who is an artist.
    for house in houses:
        problem.addConstraint(
            lambda name, occupation: not (name == 'Arnold' and occupation != 'artist') and
                                   not (occupation == 'artist' and name != 'Arnold'),
            [f'name_{house}', f'occupation_{house}']
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Occupation", "CarModel"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f'name_{house}']
        occupation = solution[f'occupation_{house}']
        car = solution[f'car_{house}']
        rows.append([str(house), name, occupation, car])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))