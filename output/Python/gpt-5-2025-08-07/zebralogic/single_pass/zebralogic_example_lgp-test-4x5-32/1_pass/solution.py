import itertools, json

def solve():
    houses = [1, 2, 3, 4]  # positions left to right
    names = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies = ['cooking', 'painting', 'photography', 'gardening']
    birthdays = ['april', 'jan', 'sept', 'feb']
    education = ['master', 'bachelor', 'associate', 'high school']
    smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']

    # Helper lambdas
    def idx_of(seq, val): return seq.index(val)
    def next_to(a, b): return abs(a - b) == 1
    def dist(a, b): return abs(a - b)

    solutions = []

    # Permute attributes with early pruning
    for b in itertools.permutations(birthdays):
        # 9 & 4: High school is the person whose birthday is in September is in the third house.
        # So birthday at house 3 is 'sept'
        if b[2] != 'sept':
            continue

        for e in itertools.permutations(education):
            # house 3 is 'high school'
            if e[2] != 'high school':
                continue

            # 7 & 12: master <-> painting and painting <-> feb => master, painting, feb are same house
            # Check existence of consistent positions later with hobby loop.

            for h in itertools.permutations(hobbies):
                # painting == feb
                if idx_of(h, 'painting') != idx_of(b, 'feb'):
                    continue
                # master == painting
                if idx_of(e, 'master') != idx_of(h, 'painting'):
                    continue

                for n in itertools.permutations(names):
                    # 6: Arnold == associate
                    if idx_of(n, 'Arnold') != idx_of(e, 'associate'):
                        continue
                    # 2 & 3: Eric == bachelor == jan
                    if idx_of(n, 'Eric') != idx_of(e, 'bachelor'):
                        continue
                    if idx_of(n, 'Eric') != idx_of(b, 'jan'):
                        continue
                    # 10: Alice == cooking
                    if idx_of(n, 'Alice') != idx_of(h, 'cooking'):
                        continue

                    for s in itertools.permutations(smoothies):
                        # 8: one house between dragonfruit and sept
                        if dist(idx_of(s, 'dragonfruit'), idx_of(b, 'sept')) != 2:
                            continue
                        # 5: Watermelon not in the third house (index 2)
                        if s[2] == 'watermelon':
                            continue
                        # 1: Desert == Jan
                        if idx_of(s, 'desert') != idx_of(b, 'jan'):
                            continue

                        # All constraints satisfied
                        solutions.append((n, h, b, e, s))

    # Choose the solution (expecting uniqueness)
    if not solutions:
        raise RuntimeError("No solution found.")
    n, h, b, e, s = solutions[0]

    # Build output rows
    rows = []
    for i in range(4):
        row = [
            str(houses[i]),
            n[i],
            h[i],
            b[i],
            e[i],
            s[i]
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve()