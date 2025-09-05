import itertools
import json

def solve():
    houses = [0, 1, 2]  # indices for houses 1..3

    categories = {
        "Name": ["Eric", "Arnold", "Peter"],
        "Vacation": ["mountain", "city", "beach"],
        "Height": ["very short", "average", "short"],
        "Flower": ["carnations", "daffodils", "lilies"],
        "HairColor": ["brown", "black", "blonde"],
        "Education": ["associate", "bachelor", "high school"],
    }

    perms = {k: list(itertools.permutations(v)) for k, v in categories.items()}

    order = ["Vacation", "HairColor", "Education", "Name", "Flower", "Height"]

    def check(state):
        # Helper to get index if category present, else None
        def idx(cat, value):
            if cat in state:
                return state[cat].index(value)
            return None

        # Clue 4: Beach is in the first house (house index 0)
        if "Vacation" in state:
            if state["Vacation"][0] != "beach":
                return False

        # Clue 10: Blonde hair is in the third house (house index 2)
        if "HairColor" in state:
            if state["HairColor"][2] != "blonde":
                return False

        # Clue 5: High school is in the third house
        if "Education" in state:
            if state["Education"][2] != "high school":
                return False

        # Clue 3: Very short is not in the second house (index 1)
        if "Height" in state:
            if state["Height"][1] == "very short":
                return False

        # Clue 6: Short is to the right of Very short
        if "Height" in state:
            if not (state["Height"].index("short") > state["Height"].index("very short")):
                return False

        # Clue 1: Peter is average height
        if "Name" in state and "Height" in state:
            if state["Name"].index("Peter") != state["Height"].index("average"):
                return False

        # Clue 2: Daffodils is Arnold
        if "Name" in state and "Flower" in state:
            if state["Flower"].index("daffodils") != state["Name"].index("Arnold"):
                return False

        # Clue 7: Lilies is Eric
        if "Name" in state and "Flower" in state:
            if state["Flower"].index("lilies") != state["Name"].index("Eric"):
                return False

        # Clue 8: Lilies is Bachelor's degree
        if "Flower" in state and "Education" in state:
            if state["Flower"].index("lilies") != state["Education"].index("bachelor"):
                return False

        # Clue 9: City is to the right of Peter
        if "Name" in state and "Vacation" in state:
            if state["Vacation"].index("city") <= state["Name"].index("Peter"):
                return False

        # Clue 11: Beach vacations -> brown hair
        if "Vacation" in state and "HairColor" in state:
            if state["HairColor"][state["Vacation"].index("beach")] != "brown":
                return False

        return True

    solution_state = None

    def backtrack(i, state):
        nonlocal solution_state
        if i == len(order):
            if check(state):
                solution_state = dict(state)
            return

        cat = order[i]
        for perm in perms[cat]:
            state[cat] = perm
            if check(state):
                backtrack(i + 1, state)
                if solution_state is not None:
                    return
            del state[cat]

    backtrack(0, {})

    if solution_state is None:
        raise RuntimeError("No solution found")

    names = solution_state["Name"]
    vacations = solution_state["Vacation"]
    heights = solution_state["Height"]
    flowers = solution_state["Flower"]
    hair = solution_state["HairColor"]
    education = solution_state["Education"]

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": []
        }
    }

    for i in range(3):
        row = [
            str(i + 1),
            names[i],
            vacations[i],
            heights[i],
            flowers[i],
            hair[i],
            education[i],
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()