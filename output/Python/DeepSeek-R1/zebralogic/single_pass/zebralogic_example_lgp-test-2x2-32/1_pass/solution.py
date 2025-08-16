import itertools
import json

def main():
    names = ['Eric', 'Arnold']
    genres = ['science fiction', 'mystery']
    num_houses = 2
    solution_rows = None

    for name_perm in itertools.permutations(names):
        for genre_perm in itertools.permutations(genres):
            rows = []
            for i in range(num_houses):
                house_num = str(i + 1)
                row = [house_num, name_perm[i], genre_perm[i]]
                rows.append(row)
            
            valid = False
            for idx, row in enumerate(rows):
                if row[1] == 'Eric':
                    if idx < num_houses - 1:
                        if rows[idx + 1][2] == 'mystery':
                            valid = True
                    break
            if valid:
                solution_rows = rows
                break
        if solution_rows is not None:
            break
    
    solution = {
        "header": ["House", "Name", "BookGenre"],
        "rows": solution_rows if solution_rows else []
    }
    output = {"solution": solution}
    print(json.dumps(output))

if __name__ == "__main__":
    main()