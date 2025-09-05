import itertools
import json

def solve_puzzle():
    names = ["Eric", "Peter", "Arnold"]
    mothers = ["Holly", "Aniya", "Janelle"]
    foods = ["pizza", "grilled cheese", "spaghetti"]
    houses = [1, 2, 3]
    
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for food_perm in itertools.permutations(foods):
                # Clue 3: The person who loves eating grilled cheese is Eric.
                try:
                    grilled_index = food_perm.index("grilled cheese")
                except ValueError:
                    continue
                if name_perm[grilled_index] != "Eric":
                    continue

                # Clue 2: The person who loves eating grilled cheese is directly left of 
                # the person whose mother's name is Aniya.
                # That means the house immediately to the right of the grilled cheese eater
                # must have mother Aniya.
                if grilled_index == len(food_perm) - 1 or mother_perm[grilled_index + 1] != "Aniya":
                    continue

                # Clue 4: Peter is the person whose mother's name is Holly.
                try:
                    peter_index = name_perm.index("Peter")
                except ValueError:
                    continue
                if mother_perm[peter_index] != "Holly":
                    continue

                # Clue 1: The person who loves spaghetti is next to Peter.
                try:
                    spaghetti_index = food_perm.index("spaghetti")
                except ValueError:
                    continue
                if abs(spaghetti_index - peter_index) != 1:
                    continue

                # If all constraints are met, build the solution rows.
                solution_rows = []
                for i in range(len(houses)):
                    row = [str(houses[i]), name_perm[i], mother_perm[i], food_perm[i]]
                    solution_rows.append(row)
                return solution_rows
    return None

def main():
    solution_rows = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": solution_rows if solution_rows is not None else []
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()