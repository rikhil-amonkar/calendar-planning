import json
from itertools import permutations

def solve_puzzle():
    # Houses numbered 1..3 (indices 0..2 in lists)
    houses = [0, 1, 2]

    # Attributes
    names_set = ["Eric", "Peter", "Arnold"]
    mothers_set = ["Holly", "Aniya", "Janelle"]
    foods_set = ["pizza", "grilled cheese", "spaghetti"]

    solutions = []

    # Helper functions
    def idx(lst, value):
        return lst.index(value)

    def is_left_of(a, b):
        # a directly left of b (a = b - 1)
        return a + 1 == b

    def is_next_to(a, b):
        return abs(a - b) == 1

    for names in permutations(names_set):
        # Clue 3: The person who loves eating grilled cheese is Eric.
        # We'll enforce after foods are assigned; just keep in mind.
        for mothers in permutations(mothers_set):
            # Clue 4: Peter is The person whose mother's name is Holly.
            if idx(names, "Peter") != idx(mothers, "Holly"):
                continue

            for foods in permutations(foods_set):
                # Uniqueness across rows already guaranteed by permutations

                # Clue 3: Eric eats grilled cheese
                if idx(names, "Eric") != idx(foods, "grilled cheese"):
                    continue

                # Clue 2: The grilled cheese eater is directly left of the person whose mother is Aniya
                if not is_left_of(idx(foods, "grilled cheese"), idx(mothers, "Aniya")):
                    continue

                # Clue 1: The person who loves the spaghetti eater and Peter are next to each other.
                # Interpret as: There exists a person (L) who loves the spaghetti eater (S),
                # and L and Peter live in adjacent houses. L cannot be S (distinct people).
                house_peter = idx(names, "Peter")
                house_spaghetti = idx(foods, "spaghetti")

                # Neighbors of Peter
                neighbors = []
                if house_peter - 1 in houses:
                    neighbors.append(house_peter - 1)
                if house_peter + 1 in houses:
                    neighbors.append(house_peter + 1)

                # There must exist a neighbor who is not the spaghetti eater
                exists_lover_neighbor = any(n != house_spaghetti for n in neighbors)
                if not exists_lover_neighbor:
                    continue

                # If all constraints satisfied, record solution
                solutions.append({
                    "names": list(names),
                    "mothers": list(mothers),
                    "foods": list(foods),
                })

    if not solutions:
        raise RuntimeError("No solution found with the given constraints.")

    # Choose a deterministic solution (e.g., lexicographically smallest by (names, mothers, foods))
    solutions.sort(key=lambda s: (tuple(s["names"]), tuple(s["mothers"]), tuple(s["foods"])))
    sol = solutions[0]

    # Prepare JSON output
    header = ["House", "Name", "Mother", "Food"]
    rows = []
    for i in range(3):
        rows.append([str(i + 1), sol["names"][i], sol["mothers"][i], sol["foods"][i]])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))