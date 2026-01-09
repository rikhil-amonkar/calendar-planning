import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-5)
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for each attribute
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'birthday_{house}', birthdays)
        problem.addVariable(f'cigar_{house}', cigars)
        problem.addVariable(f'drink_{house}', drinks)
    
    # All attributes must be unique
    problem.addConstraint(AllDifferentConstraint(), [f'name_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'birthday_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'cigar_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'drink_{h}' for h in houses])
    
    # Clue 1: The root beer lover is Eric
    for house in houses:
        problem.addConstraint(
            lambda drink, name: not (drink == 'root beer') or (name == 'Eric'),
            [f'drink_{house}', f'name_{house}']
        )
    
    # Clue 2: The person partial to Pall Mall is in the third house
    problem.addConstraint(lambda cigar: cigar == 'pall mall', ['cigar_3'])
    
    # Clue 3: The person whose birthday is in April is Bob
    for house in houses:
        problem.addConstraint(
            lambda birthday, name: not (birthday == 'april') or (name == 'Bob'),
            [f'birthday_{house}', f'name_{house}']
        )
    
    # Clue 4: The Dunhill smoker is the person whose birthday is in March
    for house in houses:
        problem.addConstraint(
            lambda cigar, birthday: not (cigar == 'dunhill') or (birthday == 'mar'),
            [f'cigar_{house}', f'birthday_{house}']
        )
    
    # Clue 5: Peter is somewhere to the right of the root beer lover
    for peter_house in houses:
        for rootbeer_house in houses:
            if peter_house <= rootbeer_house:
                continue
            problem.addConstraint(
                lambda name_p, drink_r, house_p=peter_house, house_r=rootbeer_house: 
                    not (name_p == 'Peter' and drink_r == 'root beer') or (house_p > house_r),
                [f'name_{peter_house}', f'drink_{rootbeer_house}']
            )
    
    # Clue 6: There is one house between the person whose birthday is in January and Peter
    for jan_house in houses:
        for peter_house in houses:
            if abs(jan_house - peter_house) == 2:  # One house between means difference of 2
                problem.addConstraint(
                    lambda birthday_j, name_p, house_j=jan_house, house_p=peter_house:
                        not (birthday_j == 'jan' and name_p == 'Peter') or (abs(house_j - house_p) == 2),
                    [f'birthday_{jan_house}', f'name_{peter_house}']
                )
    
    # Clue 7: The person who smokes many unique blends is the person whose birthday is in February
    for house in houses:
        problem.addConstraint(
            lambda cigar, birthday: not (cigar == 'blends') or (birthday == 'feb'),
            [f'cigar_{house}', f'birthday_{house}']
        )
    
    # Clue 8: The person whose birthday is in February is in the second house
    problem.addConstraint(lambda birthday: birthday == 'feb', ['birthday_2'])
    
    # Clue 9: Arnold is directly left of Peter
    for house in range(1, 5):  # Arnold can only be in houses 1-4
        problem.addConstraint(
            lambda name_a, name_p, house_a=house: 
                not (name_a == 'Arnold' and name_p == 'Peter') or (house_a + 1 == house),
            [f'name_{house}', f'name_{house+1}']
        )
    
    # Clue 10: The person who likes milk is not in the fifth house
    problem.addConstraint(lambda drink: drink != 'milk', ['drink_5'])
    
    # Clue 11: The person who smokes Blue Master is the coffee drinker
    for house in houses:
        problem.addConstraint(
            lambda cigar, drink: not (cigar == 'blue master') or (drink == 'coffee'),
            [f'cigar_{house}', f'drink_{house}']
        )
    
    # Clue 12: There is one house between the tea drinker and the coffee drinker
    for tea_house in houses:
        for coffee_house in houses:
            if abs(tea_house - coffee_house) == 2:  # One house between means difference of 2
                problem.addConstraint(
                    lambda drink_t, drink_c, house_t=tea_house, house_c=coffee_house:
                        not (drink_t == 'tea' and drink_c == 'coffee') or (abs(house_t - house_c) == 2),
                    [f'drink_{tea_house}', f'drink_{coffee_house}']
                )
    
    # Clue 13: Eric is in the third house
    problem.addConstraint(lambda name: name == 'Eric', ['name_3'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Birthday", "Cigar", "Drink"], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    rows = []
    for house in houses:
        name = solution[f'name_{house}']
        birthday = solution[f'birthday_{house}']
        cigar = solution[f'cigar_{house}']
        drink = solution[f'drink_{house}']
        rows.append([str(house), name, birthday, cigar, drink])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))