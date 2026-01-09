import json
from itertools import permutations, product

def main():
    # Define houses and categories
    houses = [1, 2]
    categories = {
        "Name": ["Eric", "Arnold"],
        "Hobby": ["gardening", "photography"],
        "BookGenre": ["science fiction", "mystery"],
        "MusicGenre": ["rock", "pop"],
        "Birthday": ["april", "sept"],
    }

    # Build all bijective assignments for each category (AllDifferent within category)
    category_options = []
    for category, values in categories.items():
        opts = []
        for perm in permutations(houses, len(values)):
            mapping = {}
            for i, v in enumerate(values):
                mapping[(category, v)] = perm[i]
            opts.append(mapping)
        category_options.append(opts)

    # Search for solutions satisfying the constraints
    solutions = []
    for combo in product(*category_options):
        # Merge mappings
        sol = {}
        for m in combo:
            sol.update(m)

        # Constraints:
        # 1. The person who loves mystery books is the person who loves rock music.
        if sol[("BookGenre", "mystery")] != sol[("MusicGenre", "rock")]:
            continue

        # 2. Arnold is not in the first house.
        if sol[("Name", "Arnold")] == 1:
            continue

        # 3. The person who loves mystery books is the person who enjoys gardening.
        if sol[("BookGenre", "mystery")] != sol[("Hobby", "gardening")]:
            continue

        # 4. The person whose birthday is in April is Arnold.
        if sol[("Birthday", "april")] != sol[("Name", "Arnold")]:
            continue

        # 5. The person who loves mystery books is in the first house.
        if sol[("BookGenre", "mystery")] != 1:
            continue

        solutions.append(sol)

    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    sol = solutions[0]

    # Build the output rows in house order
    header = ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"]

    def value_in_house(category, house):
        for v in categories[category]:
            if sol[(category, v)] == house:
                return v
        return None

    rows = []
    for h in houses:
        row = [
            str(h),
            value_in_house("Name", h),
            value_in_house("Hobby", h),
            value_in_house("BookGenre", h),
            value_in_house("MusicGenre", h),
            value_in_house("Birthday", h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()