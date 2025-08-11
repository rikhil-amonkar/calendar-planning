import itertools
import json

def main():
    n_houses = 6
    name_assignment = [None] * n_houses
    cigar_assignment = [None] * n_houses

    name_assignment[0] = 'Peter'
    name_assignment[2] = 'Bob'
    name_assignment[4] = 'Carol'
    name_assignment[5] = 'Eric'

    cigar_assignment[2] = 'pall mall'
    cigar_assignment[4] = 'blue master'

    remaining_names = ['Arnold', 'Alice']
    remaining_cigars = ['blends', 'yellow monster', 'dunhill', 'prince']

    solution_found = False
    for name_perm in itertools.permutations(remaining_names):
        name_assignment[1] = name_perm[0]
        name_assignment[3] = name_perm[1]

        for cigar_perm in itertools.permutations(remaining_cigars):
            cigar_assignment[0] = cigar_perm[0]
            cigar_assignment[1] = cigar_perm[1]
            cigar_assignment[3] = cigar_perm[2]
            cigar_assignment[5] = cigar_perm[3]

            try:
                arnold_index = name_assignment.index('Arnold')
                blends_index = cigar_assignment.index('blends')
                if arnold_index >= blends_index:
                    continue
            except ValueError:
                continue

            try:
                prince_index = cigar_assignment.index('prince')
                if arnold_index >= prince_index:
                    continue
            except ValueError:
                continue

            try:
                yellow_index = cigar_assignment.index('yellow monster')
                blends_index = cigar_assignment.index('blends')
                if abs(yellow_index - blends_index) != 2:
                    continue
            except ValueError:
                continue

            solution_found = True
            break
        if solution_found:
            break

    if not solution_found:
        print(json.dumps({"error": "No solution found"}))
        return

    header = ["House", "Name", "favorite cigar"]
    rows = []
    for i in range(n_houses):
        house_number = str(i+1)
        name = name_assignment[i]
        cigar = cigar_assignment[i]
        rows.append([house_number, name, cigar])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()