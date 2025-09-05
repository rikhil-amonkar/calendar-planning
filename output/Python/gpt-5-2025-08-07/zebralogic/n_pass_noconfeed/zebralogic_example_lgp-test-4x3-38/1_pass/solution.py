import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
    flowers = ['carnations', 'roses', 'lilies', 'daffodils']

    solutions = []

    for perm_names in itertools.permutations(names):
        # 8. Alice is in the third house.
        idx_Alice = perm_names.index('Alice')
        if idx_Alice != 2:
            continue

        idx_Arnold = perm_names.index('Arnold')
        idx_Eric = perm_names.index('Eric')
        idx_Peter = perm_names.index('Peter')

        for perm_mothers in itertools.permutations(mothers):
            # 1. Alice is The person whose mother's name is Kailyn.
            if perm_mothers[idx_Alice] != 'Kailyn':
                continue

            # 5. Arnold is The person whose mother's name is Holly.
            if perm_mothers[idx_Arnold] != 'Holly':
                continue

            # 2. The person whose mother's name is Janelle is somewhere to the right of Arnold.
            idx_Janelle = perm_mothers.index('Janelle')
            if not (idx_Janelle > idx_Arnold):
                continue

            idx_Holly = perm_mothers.index('Holly')  # same as idx_Arnold due to clue 5

            # Now assign flowers
            for perm_flowers in itertools.permutations(flowers):
                # 7. The person who loves the boquet of lilies is directly left of Alice.
                idx_lilies = perm_flowers.index('lilies')
                if not (idx_lilies + 1 == idx_Alice):
                    continue

                # 4. Eric is the person who loves a bouquet of daffodils.
                if perm_flowers[idx_Eric] != 'daffodils':
                    continue

                # 3. Peter is somewhere to the right of the person who loves a carnations arrangement.
                idx_carnations = perm_flowers.index('carnations')
                if not (idx_Peter > idx_carnations):
                    continue

                # 6. The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly.
                if not (idx_carnations > idx_Holly):
                    continue

                # If all constraints satisfied, record solution
                solutions.append((perm_names, perm_mothers, perm_flowers))

    if not solutions:
        raise RuntimeError("No solution found.")
    if len(solutions) > 1:
        # If multiple, we still output the first valid one, but this indicates non-uniqueness.
        solution = solutions[0]
    else:
        solution = solutions[0]

    perm_names, perm_mothers, perm_flowers = solution

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": [
                [str(i+1), perm_names[i], perm_mothers[i], perm_flowers[i]]
                for i in range(4)
            ]
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))