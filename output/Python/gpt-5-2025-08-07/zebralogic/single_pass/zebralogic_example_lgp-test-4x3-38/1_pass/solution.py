import json
import itertools

def solve_puzzle():
    houses = [0, 1, 2, 3]  # indices for houses 1..4
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
    flowers = ['carnations', 'roses', 'lilies', 'daffodils']

    solutions = []

    for name_perm in itertools.permutations(names):
        # Clue 8: Alice is in the third house (index 2)
        if name_perm[2] != 'Alice':
            continue

        pos_name = {name: idx for idx, name in enumerate(name_perm)}

        for mother_perm in itertools.permutations(mothers):
            # Clue 1: Alice's mother is Kailyn
            if mother_perm[pos_name['Alice']] != 'Kailyn':
                continue
            # Clue 5: Arnold's mother is Holly
            if mother_perm[pos_name['Arnold']] != 'Holly':
                continue
            # Clue 2: Janelle is somewhere to the right of Arnold
            if mother_perm.index('Janelle') <= pos_name['Arnold']:
                continue

            for flower_perm in itertools.permutations(flowers):
                # Clue 7: Lilies is directly left of Alice
                if flower_perm.index('lilies') + 1 != pos_name['Alice']:
                    continue
                # Clue 4: Eric has daffodils
                if flower_perm[pos_name['Eric']] != 'daffodils':
                    continue
                # Clue 3: Peter is somewhere to the right of carnations
                if pos_name['Peter'] <= flower_perm.index('carnations'):
                    continue
                # Clue 6: Carnations is to the right of Holly (Holly is at Arnold's house)
                if flower_perm.index('carnations') <= mother_perm.index('Holly'):
                    continue

                # All constraints satisfied; record solution
                solutions.append((name_perm, mother_perm, flower_perm))

    # Expect exactly one solution
    if not solutions:
        raise RuntimeError("No solution found.")
    # If multiple solutions found, choose the first (puzzle should be unique)
    name_sol, mother_sol, flower_sol = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": []
        }
    }

    for i in range(4):
        row = [str(i + 1), name_sol[i], mother_sol[i], flower_sol[i]]
        result["solution"]["rows"].append(row)

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()