import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            if (name_perm.index("Bob") < child_perm.index("Samantha") and
                name_perm.index(name_perm[child_perm.index("Timothy")]) < child_perm.index("Samantha") and
                child_perm[1] == "Fred" and
                abs(name_perm.index(name_perm[child_perm.index("Samantha")]) - name_perm.index("Alice")) == 2 and
                name_perm[2] != "Eric" and
                name_perm[2] != "Bob" and
                child_perm.index("Fred") + 1 == child_perm.index("Bella") and
                name_perm.index(name_perm[child_perm.index("Samantha")]) < name_perm.index("Peter")):
                
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Children"],
                        "rows": []
                    }
                }
                for i in range(5):
                    solution["solution"]["rows"].append([str(i+1), name_perm[i], child_perm[i]])
                return json.dumps(solution)

print(solve_puzzle())