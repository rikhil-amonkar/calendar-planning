import json
from itertools import permutations

def main():
    # Define categories and domains
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]

    # Brute-force search (avoids external 'constraint' dependency)
    solution = None
    for name_perm in permutations(houses, len(names)):
        name_assign = {names[i]: name_perm[i] for i in range(len(names))}

        for birth_perm in permutations(houses, len(birthdays)):
            birth_assign = {birthdays[i]: birth_perm[i] for i in range(len(birthdays))}
            # Clue 2: April is in the first house.
            if birth_assign["april"] != 1:
                continue

            for color_perm in permutations(houses, len(colors)):
                color_assign = {colors[i]: color_perm[i] for i in range(len(colors))}
                # Clue 1: Eric is the person who loves yellow.
                if name_assign["Eric"] != color_assign["yellow"]:
                    continue
                # Clue 3: The person who loves yellow is not in the first house.
                if color_assign["yellow"] == 1:
                    continue

                solution = {**name_assign, **birth_assign, **color_assign}
                break
            if solution:
                break
        if solution:
            break

    if not solution:
        raise ValueError("No solution found for the given puzzle.")

    # Build rows per house in order
    rows = []
    for h in sorted(houses):
        name = next(n for n in names if solution[n] == h)
        birthday = next(b for b in birthdays if solution[b] == h)
        color = next(c for c in colors if solution[c] == h)
        rows.append([str(h), name, birthday, color])

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()