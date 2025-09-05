import json
import itertools

def solve_puzzle():
    # Define houses and attributes
    houses = [1, 2, 3]
    names = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']

    solutions = []

    # Iterate over all permutations for names, occupations, and hobbies
    for names_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            # Constraint 5: The person who is an engineer is Peter.
            # Peter and engineer must be in the same house.
            if names_perm.index('Peter') != occ_perm.index('engineer'):
                continue

            for hob_perm in itertools.permutations(hobbies):
                # Helper to find index (0-based) of values
                idx_name = lambda n: names_perm.index(n)
                idx_occ = lambda o: occ_perm.index(o)
                idx_hob = lambda h: hob_perm.index(h)

                # Constraint 4: The photography enthusiast is the person who is a teacher.
                if idx_hob('photography') != idx_occ('teacher'):
                    continue

                # Constraint 2: The person who loves cooking is directly left of the person who is a teacher.
                if not (idx_hob('cooking') + 1 == idx_occ('teacher')):
                    continue

                # Constraint 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
                if not (idx_occ('doctor') > idx_hob('gardening')):
                    continue

                # Constraint 1: The person who is a doctor and Eric are next to each other.
                if abs(idx_occ('doctor') - idx_name('Eric')) != 1:
                    continue

                # If all constraints are satisfied, record the solution
                solution_rows = []
                for i, house in enumerate(houses):
                    row = [
                        str(house),
                        names_perm[i],
                        occ_perm[i],
                        hob_perm[i]
                    ]
                    solution_rows.append(row)

                solutions.append({
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": solution_rows
                    }
                })

    # Assuming a unique solution exists
    if solutions:
        return solutions[0]
    else:
        # In case no solution is found, return an empty structured response
        return {
            "solution": {
                "header": ["House", "Name", "Occupation", "Hobby"],
                "rows": []
            }
        }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))