import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']
    
    houses = [1, 2, 3, 4, 5]
    
    # Add variables for each attribute per house
    for i in houses:
        problem.addVariable(f'name_{i}', names)
        problem.addVariable(f'smoothie_{i}', smoothies)
        problem.addVariable(f'animal_{i}', animals)
        problem.addVariable(f'nationality_{i}', nationalities)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f'name_{i}' for i in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'smoothie_{i}' for i in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'animal_{i}' for i in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'nationality_{i}' for i in houses])
    
    # Clue 1: The Swedish person is directly left of the dog owner.
    for i in range(1, 5):
        problem.addConstraint(
            lambda nat, anim, house1=i: not(nat == 'swede' and anim == 'dog') or (nat == 'swede' and anim == 'dog' and house1 + 1 <= 5),
            [f'nationality_{i}', f'animal_{i}']
        )
    for i in range(1, 6):
        for j in range(1, 6):
            if i != j:
                problem.addConstraint(
                    lambda nat_i, anim_j, house_i=i, house_j=j: not(nat_i == 'swede' and anim_j == 'dog') or (house_j == house_i + 1),
                    [f'nationality_{i}', f'animal_{j}']
                )
    
    # Clue 2: There are two houses between the dog owner and the British person.
    for i in range(1, 6):
        for j in range(1, 6):
            if abs(i - j) == 3:
                problem.addConstraint(
                    lambda anim_i, nat_j, house_i=i, house_j=j: not(anim_i == 'dog' and nat_j == 'brit') or True,
                    [f'animal_{i}', f'nationality_{j}']
                )
            else:
                problem.addConstraint(
                    lambda anim_i, nat_j, house_i=i, house_j=j: not(anim_i == 'dog' and nat_j == 'brit') or False,
                    [f'animal_{i}', f'nationality_{j}']
                )
    
    # Clue 3: The Dane is the person who keeps horses.
    for i in houses:
        problem.addConstraint(
            lambda nat, anim: not(nat == 'dane') or (anim == 'horse'),
            [f'nationality_{i}', f'animal_{i}']
        )
    
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    for i in range(1, 6):
        for j in range(1, 6):
            if i >= j:
                problem.addConstraint(
                    lambda anim_i, anim_j, house_i=i, house_j=j: not(anim_i == 'bird' and anim_j == 'cat') or False,
                    [f'animal_{i}', f'animal_{j}']
                )
    
    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
    for i in range(1, 5):
        problem.addConstraint(
            lambda anim_i, smoothie_j, house_i=i: not(anim_i == 'dog') or (smoothie_j == 'lime' and house_i + 1 <= 5),
            [f'animal_{i}', f'smoothie_{i+1}']
        )
    
    # Clue 6: Eric is the cat lover.
    for i in houses:
        problem.addConstraint(
            lambda name, anim: not(name == 'Eric') or (anim == 'cat'),
            [f'name_{i}', f'animal_{i}']
        )
    
    # Clue 7: Bob is the bird keeper.
    for i in houses:
        problem.addConstraint(
            lambda name, anim: not(name == 'Bob') or (anim == 'bird'),
            [f'name_{i}', f'animal_{i}']
        )
    
    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
    for i in range(1, 5):
        problem.addConstraint(
            lambda smoothie_i, name_j, house_i=i: not(smoothie_i == 'cherry') or (name_j == 'Peter' and house_i + 1 <= 5),
            [f'smoothie_{i}', f'name_{i+1}']
        )
    
    # Clue 9: The bird keeper is the Watermelon smoothie lover.
    for i in houses:
        problem.addConstraint(
            lambda anim, smoothie: not(anim == 'bird') or (smoothie == 'watermelon'),
            [f'animal_{i}', f'smoothie_{i}']
        )
    
    # Clue 10: The Desert smoothie lover is the dog owner.
    for i in houses:
        problem.addConstraint(
            lambda smoothie, anim: not(smoothie == 'desert') or (anim == 'dog'),
            [f'smoothie_{i}', f'animal_{i}']
        )
    
    # Clue 11: The person who keeps horses is in the third house.
    problem.addConstraint(lambda anim: anim == 'horse', ['animal_3'])
    
    # Clue 12: The Norwegian is Alice.
    for i in houses:
        problem.addConstraint(
            lambda nat, name: not(nat == 'norwegian') or (name == 'Alice'),
            [f'nationality_{i}', f'name_{i}']
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Smoothie", "Animal", "Nationality"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for i in houses:
        row = [
            str(i),
            solution[f'name_{i}'],
            solution[f'smoothie_{i}'],
            solution[f'animal_{i}'],
            solution[f'nationality_{i}']
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))