import itertools
import json

def solve_puzzle():
    # Define attributes
    houses = [1, 2, 3]

    Names = ["Peter", "Arnold", "Eric"]
    BookGenres = ["science fiction", "mystery", "romance"]
    Smoothies = ["watermelon", "desert", "cherry"]
    Birthdays = ["april", "jan", "sept"]
    Heights = ["average", "very short", "short"]

    def make_maps(seq):
        # seq is a tuple of values assigned to houses [1..n] in order
        house_to_val = {i + 1: v for i, v in enumerate(seq)}
        val_to_house = {v: i + 1 for i, v in enumerate(seq)}
        return house_to_val, val_to_house

    solutions = []

    for smoothie_perm in itertools.permutations(Smoothies):
        sm_h2v, sm_v2h = make_maps(smoothie_perm)

        # 1. The person who likes Cherry smoothies is not in the second house.
        if sm_v2h["cherry"] == 2:
            continue

        for height_perm in itertools.permutations(Heights):
            ht_h2v, ht_v2h = make_maps(height_perm)

            # 8. The Watermelon smoothie lover is the person who is short.
            if sm_v2h["watermelon"] != ht_v2h["short"]:
                continue

            # 6. The person who has an average height is the Desert smoothie lover.
            if ht_v2h["average"] != sm_v2h["desert"]:
                continue

            for book_perm in itertools.permutations(BookGenres):
                bk_h2v, bk_v2h = make_maps(book_perm)

                # 4. The person who is very short is the person who loves romance books.
                if ht_v2h["very short"] != bk_v2h["romance"]:
                    continue

                for bday_perm in itertools.permutations(Birthdays):
                    bd_h2v, bd_v2h = make_maps(bday_perm)

                    # 3. The person whose birthday is in January is not in the first house.
                    if bd_v2h["jan"] == 1:
                        continue

                    # 5. The person who loves mystery books is the person whose birthday is in September.
                    if bk_v2h["mystery"] != bd_v2h["sept"]:
                        continue

                    for name_perm in itertools.permutations(Names):
                        nm_h2v, nm_v2h = make_maps(name_perm)

                        # 7. Eric is in the first house.
                        if nm_v2h["Eric"] != 1:
                            continue

                        # 9. The Watermelon smoothie lover is Eric.
                        if sm_v2h["watermelon"] != nm_v2h["Eric"]:
                            continue

                        # 2. Arnold is the person who loves mystery books.
                        if nm_v2h["Arnold"] != bk_v2h["mystery"]:
                            continue

                        # If all constraints satisfied, record solution
                        solution_rows = []
                        for h in houses:
                            row = [
                                str(h),
                                nm_h2v[h],
                                bk_h2v[h],
                                sm_h2v[h],
                                bd_h2v[h],
                                ht_h2v[h],
                            ]
                            solution_rows.append(row)

                        solutions.append(solution_rows)

    if not solutions:
        raise RuntimeError("No solution found.")
    # Choose the first (should be unique)
    rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))