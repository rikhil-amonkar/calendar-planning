import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
    heights = ["average", "very tall", "very short", "short", "tall"]
    cigars = ["prince", "dunhill", "blends", "pall mall", "blue master"]
    smoothies = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
    phones = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

    for perm in itertools.permutations(names):
        if perm[2] != "Eric" or perm[4] != "Alice":
            continue

        for h_perm in itertools.permutations(heights):
            if h_perm[perm.index("Eric")] != "very tall" or h_perm[perm.index("Bob")] != "average":
                continue

            for c_perm in itertools.permutations(cigars):
                if c_perm[perm.index("Bob")] != "dunhill" or c_perm[perm.index("Eric")] != "prince":
                    continue

                for s_perm in itertools.permutations(smoothies):
                    if s_perm[c_perm.index("prince")] != "desert" or s_perm[perm.index("Bob")] != "dragonfruit" or s_perm[perm.index("Eric")] != "cherry":
                        continue

                    for p_perm in itertools.permutations(phones):
                        if p_perm[perm.index("Eric")] != "iphone 13" or p_perm[p_perm.index("iphone 13") + 1] != "blue master" or p_perm[h_perm.index("short")] != "samsung galaxy s21" or abs(p_perm.index("iphone 13") - p_perm.index("oneplus 9")) != 1 or abs(h_perm.index("very tall") - s_perm.index("dragonfruit")) != 2 or p_perm[perm.index("Arnold") + 1] == "huawei p50" or perm.index("Bob") == 3 or s_perm.index("desert") >= s_perm.index("lime"):
                            continue

                        if abs(perm.index("Eric") - perm.index("Alice")) != 2 and abs(perm.index("Eric") - perm.index("Alice")) != 3:
                            continue

                        if abs(perm.index("Arnold") - h_perm.index("very short")) != 1:
                            continue

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "Phone"],
                                "rows": []
                            }
                        }

                        for i in range(5):
                            solution["solution"]["rows"].append([
                                str(i + 1),
                                perm[i],
                                h_perm[i],
                                c_perm[i],
                                s_perm[i],
                                p_perm[i]
                            ])

                        return json.dumps(solution, indent=2)

print(solve_puzzle())