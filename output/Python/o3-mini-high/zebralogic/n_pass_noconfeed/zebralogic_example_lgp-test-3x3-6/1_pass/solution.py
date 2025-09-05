import itertools
import json

def solve():
    names = ["Eric", "Arnold", "Peter"]
    book_genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]
    
    # There are 3 houses, indexed 0, 1, 2 corresponding to houses 1, 2, 3.
    for name_perm in itertools.permutations(names):
        for book_perm in itertools.permutations(book_genres):
            for vac_perm in itertools.permutations(vacations):
                # Clue 1: Eric is directly left of Arnold.
                if name_perm.index("Eric") + 1 != name_perm.index("Arnold"):
                    continue
                
                # Clue 3: Peter is the person who prefers city breaks.
                if vac_perm[name_perm.index("Peter")] != "city":
                    continue
                
                # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
                if name_perm.index("Peter") <= vac_perm.index("beach"):
                    continue
                
                # Clue 5: The person who loves science fiction books is the person who loves beach vacations.
                beach_house = vac_perm.index("beach")
                if book_perm[beach_house] != "science fiction":
                    continue
                
                # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
                mystery_house = book_perm.index("mystery")
                if mystery_house >= vac_perm.index("beach"):
                    continue
                
                # If all constraints are satisfied, build the solution.
                solution = []
                for i in range(3):
                    house_number = str(i + 1)
                    solution.append([house_number, name_perm[i], book_perm[i], vac_perm[i]])
                return solution
    return None

def main():
    sol = solve()
    output = {
      "solution": {
        "header": ["House", "Name", "BookGenre", "Vacation"],
        "rows": sol if sol is not None else []
      }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()