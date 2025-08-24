import json
import itertools

# Zebra puzzle solver for the given 6-house logic puzzle

houses = list(range(6))  # 0..5 represent houses 1..6

# Categories and their values
Names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
Cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
Music = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
Drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
Mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
Food = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

all_values = {
    "Name": Names,
    "Cigar": Cigars,
    "MusicGenre": Music,
    "Drink": Drinks,
    "Mother": Mothers,
    "Food": Food
}

# Helpers to access positions and values from partial assignments
def get_pos(assignments, category, value):
    arr = assignments.get(category)
    if arr is None:
        return None
    try:
        return arr.index(value)
    except ValueError:
        return None

def get_value(assignments, category, index):
    arr = assignments.get(category)
    if arr is None:
        return None
    return arr[index]

def check_directly_left(assignments, catA, valA, catB, valB):
    posA = get_pos(assignments, catA, valA)
    posB = get_pos(assignments, catB, valB)
    # Boundary impossibility if one side known
    if posA is not None and posA == 5:
        return False
    if posB is not None and posB == 0:
        return False
    if posA is not None and posB is not None:
        return posA + 1 == posB
    return True

def check_left_of(assignments, catL, valL, catR, valR):
    posL = get_pos(assignments, catL, valL)
    posR = get_pos(assignments, catR, valR)
    if posL is not None and posL == 5:
        return False
    if posR is not None and posR == 0:
        return False
    if posL is not None and posR is not None:
        return posL < posR
    return True

def check_same_house(assignments, catA, valA, catB, valB):
    posA = get_pos(assignments, catA, valA)
    posB = get_pos(assignments, catB, valB)
    if posA is not None and posB is not None:
        return posA == posB
    return True

def check_distance(assignments, catA, valA, catB, valB, dist):
    posA = get_pos(assignments, catA, valA)
    posB = get_pos(assignments, catB, valB)
    if posA is not None and posB is not None:
        return abs(posA - posB) == dist
    return True

def valid(assignments):
    # C1: Carol directly left of grilled cheese
    if not check_directly_left(assignments, "Name", "Carol", "Food", "grilled cheese"):
        return False
    # C2: Eric not in 2nd house
    arrN = assignments.get("Name")
    if arrN is not None:
        if arrN[1] == "Eric":
            return False
    # C3: Holly to the right of Carol
    if not check_left_of(assignments, "Name", "Carol", "Mother", "Holly"):
        return False
    # C4: Rock left of grilled cheese
    if not check_left_of(assignments, "MusicGenre", "rock", "Food", "grilled cheese"):
        return False
    # C5: Eric directly left of Carol
    if not check_directly_left(assignments, "Name", "Eric", "Name", "Carol"):
        return False
    # C6: Pop not in 3rd house
    arrM = assignments.get("MusicGenre")
    if arrM is not None:
        if arrM[2] == "pop":
            return False
    # C7: Eric loves country
    if not check_same_house(assignments, "Name", "Eric", "MusicGenre", "country"):
        return False
    # C8: Classical in 6th house
    if arrM is not None:
        if arrM[5] != "classical":
            return False
    # C9: Coffee is Bob
    if not check_same_house(assignments, "Name", "Bob", "Drink", "coffee"):
        return False
    # C10: Blends is Peter
    if not check_same_house(assignments, "Name", "Peter", "Cigar", "blends"):
        return False
    # C11: Stew not in 5th house
    arrF = assignments.get("Food")
    if arrF is not None:
        if arrF[4] == "stew":
            return False
    # C12: Root beer directly left of Janelle
    if not check_directly_left(assignments, "Drink", "root beer", "Mother", "Janelle"):
        return False
    # C13: Two houses between Sarah and Yellow Monster
    if not check_distance(assignments, "Mother", "Sarah", "Cigar", "yellow monster", 3):
        return False
    # C14: Eric is tea drinker
    if not check_same_house(assignments, "Name", "Eric", "Drink", "tea"):
        return False
    # C15: Pall Mall to the right of stir fry
    if not check_left_of(assignments, "Food", "stir fry", "Cigar", "pall mall"):
        return False
    # C16: Soup is Bob
    if not check_same_house(assignments, "Name", "Bob", "Food", "soup"):
        return False
    # C17: Hip hop directly left of Kailyn
    if not check_directly_left(assignments, "MusicGenre", "hip hop", "Mother", "Kailyn"):
        return False
    # C18: Arnold to the right of Kailyn
    if not check_left_of(assignments, "Mother", "Kailyn", "Name", "Arnold"):
        return False
    # C19: Water directly left of Blue Master
    if not check_directly_left(assignments, "Drink", "water", "Cigar", "blue master"):
        return False
    # C20: Spaghetti to the left of blends smoker (i.e., Peter)
    if not check_left_of(assignments, "Food", "spaghetti", "Name", "Peter"):
        return False
    # C21: Sarah directly left of Jazz
    if not check_directly_left(assignments, "Mother", "Sarah", "MusicGenre", "jazz"):
        return False
    # C22: Hip hop directly left of root beer
    if not check_directly_left(assignments, "MusicGenre", "hip hop", "Drink", "root beer"):
        return False
    # C23: Water drinker is the stew lover
    if not check_same_house(assignments, "Drink", "water", "Food", "stew"):
        return False
    # C24: Dunhill not in 2nd house
    arrC = assignments.get("Cigar")
    if arrC is not None:
        if arrC[1] == "dunhill":
            return False
    # C25: Milk drinker is Janelle
    if not check_same_house(assignments, "Drink", "milk", "Mother", "Janelle"):
        return False
    # C26: Eric is Aniya
    if not check_same_house(assignments, "Name", "Eric", "Mother", "Aniya"):
        return False

    # Additional structural implications to prune earlier:
    # From C17 + C22 + C12: hip hop at k, root beer at k+1, Janelle at k+2 (if all categories assigned appropriately)
    # We'll just rely on the direct checks above; these will be enforced when relevant categories are set.

    return True

def perm_generator_for_category(category, assignments):
    values = all_values[category]
    # Build an initial template with positional constraints if any strong ones known
    template = [None] * 6

    # Positional constraints depending on category
    if category == "MusicGenre":
        # C8: classical at house 6
        template[5] = "classical"
        # C7: Eric -> country (if Name already assigned)
        if "Name" in assignments:
            pos_eric = get_pos(assignments, "Name", "Eric")
            if pos_eric is not None:
                # Cannot place country at position 5 (if eric is 5 - but eric cannot be 5 because Carol and GC need space? It's allowed theoretically.)
                if template[pos_eric] is not None and template[pos_eric] != "country":
                    return  # conflict
                # Will set after; we'll enforce via template
                template[pos_eric] = "country"
    elif category == "Mother":
        # C26: Eric -> Aniya
        if "Name" in assignments:
            pos_eric = get_pos(assignments, "Name", "Eric")
            if pos_eric is not None:
                template[pos_eric] = "Aniya"
        # From C17: hip hop directly left of Kailyn
        if "MusicGenre" in assignments:
            pos_hip = get_pos(assignments, "MusicGenre", "hip hop")
            if pos_hip is not None:
                if pos_hip == 5:
                    return  # impossible
                if template[pos_hip + 1] is not None and template[pos_hip + 1] != "Kailyn":
                    return
                template[pos_hip + 1] = "Kailyn"
        # From C21: Sarah directly left of Jazz
        if "MusicGenre" in assignments:
            pos_jazz = get_pos(assignments, "MusicGenre", "jazz")
            if pos_jazz is not None:
                if pos_jazz == 0:
                    return  # impossible
                if template[pos_jazz - 1] is not None and template[pos_jazz - 1] != "Sarah":
                    return
                template[pos_jazz - 1] = "Sarah"
        # From C22 + C12: hip hop left of root beer and root beer left of Janelle => Janelle is two to the right of hip hop
        if "MusicGenre" in assignments:
            pos_hip = get_pos(assignments, "MusicGenre", "hip hop")
            if pos_hip is not None:
                if pos_hip >= 4:
                    return  # can't fit +2
                if template[pos_hip + 2] is not None and template[pos_hip + 2] != "Janelle":
                    return
                template[pos_hip + 2] = "Janelle"
    elif category == "Drink":
        # Bob -> coffee; Eric -> tea
        if "Name" in assignments:
            pos_bob = get_pos(assignments, "Name", "Bob")
            if pos_bob is not None:
                if template[pos_bob] is not None and template[pos_bob] != "coffee":
                    return
                template[pos_bob] = "coffee"
            pos_eric = get_pos(assignments, "Name", "Eric")
            if pos_eric is not None:
                if template[pos_eric] is not None and template[pos_eric] != "tea":
                    return
                template[pos_eric] = "tea"
        # Janelle -> milk and root beer directly left of Janelle
        if "Mother" in assignments:
            pos_jan = get_pos(assignments, "Mother", "Janelle")
            if pos_jan is not None:
                if template[pos_jan] is not None and template[pos_jan] != "milk":
                    return
                template[pos_jan] = "milk"
                if pos_jan == 0:
                    return
                if template[pos_jan - 1] is not None and template[pos_jan - 1] != "root beer":
                    return
                template[pos_jan - 1] = "root beer"
        # From C22: hip hop directly left of root beer
        if "MusicGenre" in assignments:
            pos_hip = get_pos(assignments, "MusicGenre", "hip hop")
            if pos_hip is not None:
                if pos_hip == 5:
                    return
                if template[pos_hip + 1] is not None and template[pos_hip + 1] != "root beer":
                    return
                template[pos_hip + 1] = "root beer"
    elif category == "Cigar":
        # Peter -> blends
        if "Name" in assignments:
            pos_peter = get_pos(assignments, "Name", "Peter")
            if pos_peter is not None:
                if template[pos_peter] is not None and template[pos_peter] != "blends":
                    return
                template[pos_peter] = "blends"
        # Dunhill not at 2nd is checked later, but leave template None
        # From C19: water directly left of blue master
        if "Drink" in assignments:
            pos_water = get_pos(assignments, "Drink", "water")
            if pos_water is not None:
                if pos_water == 5:
                    return
                if template[pos_water + 1] is not None and template[pos_water + 1] != "blue master":
                    return
                template[pos_water + 1] = "blue master"
    elif category == "Food":
        # Bob -> soup
        if "Name" in assignments:
            pos_bob = get_pos(assignments, "Name", "Bob")
            if pos_bob is not None:
                if template[pos_bob] is not None and template[pos_bob] != "soup":
                    return
                template[pos_bob] = "soup"
        # Carol directly left of grilled cheese
        if "Name" in assignments:
            pos_carol = get_pos(assignments, "Name", "Carol")
            if pos_carol is not None:
                if pos_carol == 5:
                    return
                if template[pos_carol + 1] is not None and template[pos_carol + 1] != "grilled cheese":
                    return
                template[pos_carol + 1] = "grilled cheese"
        # Water drinker is stew
        if "Drink" in assignments:
            pos_water = get_pos(assignments, "Drink", "water")
            if pos_water is not None:
                if template[pos_water] is not None and template[pos_water] != "stew":
                    return
                template[pos_water] = "stew"

    # Build remaining values and indices
    fixed_vals = set(v for v in template if v is not None)
    if len(fixed_vals) != sum(1 for v in template if v is not None):
        # Duplicate fixed values, impossible
        return

    remaining_values = [v for v in values if v not in fixed_vals]
    remaining_indices = [i for i, v in enumerate(template) if v is None]

    # Early impossibility checks for constraints that force values at certain indices:
    # For Music: pop not in index 2 is checked later in valid(), but we can reject permutations later.

    for perm in itertools.permutations(remaining_values, len(remaining_indices)):
        arr = template[:]
        for idx, val in zip(remaining_indices, perm):
            arr[idx] = val

        # Quick per-category local filters to prune before full valid():
        if category == "Name":
            # C2: Eric not in second
            if arr[1] == "Eric":
                continue
            # C5: Eric directly left of Carol
            if arr.index("Eric") + 1 != arr.index("Carol"):
                continue
        elif category == "MusicGenre":
            # C6: Pop not in third
            if arr[2] == "pop":
                continue
            # C8: classical in 6th (already enforced)
            pass
        elif category == "Cigar":
            # C24: Dunhill not in second
            if arr[1] == "dunhill":
                continue
            # C13: If Mother assigned and Sarah pos known, Yellow Monster must be at pos±3
            if "Mother" in assignments:
                pos_sarah = get_pos(assignments, "Mother", "Sarah")
                if pos_sarah is not None:
                    pos_ym = arr.index("yellow monster")
                    if pos_ym not in [pos_sarah - 3, pos_sarah + 3]:
                        continue
            # C19: If Drink assigned, enforce water->blue master (already in template but double-check)
            if "Drink" in assignments:
                pos_water = get_pos(assignments, "Drink", "water")
                if pos_water is not None:
                    if pos_water == 5:
                        continue
                    if arr[pos_water + 1] != "blue master":
                        continue
        elif category == "Food":
            # C11: Stew not in 5th
            if arr[4] == "stew":
                continue
            # C20: Spaghetti left of Peter (if Name assigned)
            if "Name" in assignments:
                if arr.index("spaghetti") >= get_pos(assignments, "Name", "Peter"):
                    continue

        # Yield current permutation
        yield arr

def search(assignments, categories_order, idx):
    if idx == len(categories_order):
        if valid(assignments):
            return assignments
        return None

    category = categories_order[idx]
    for arr in perm_generator_for_category(category, assignments) or []:
        assignments[category] = arr
        if valid(assignments):
            result = search(assignments, categories_order, idx + 1)
            if result is not None:
                return result
        del assignments[category]
    return None

def solve():
    categories_order = ["Name", "MusicGenre", "Mother", "Drink", "Cigar", "Food"]
    assignments = {}
    solution = search(assignments, categories_order, 0)
    if solution is None:
        raise RuntimeError("No solution found")
    # Build output rows
    header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
    rows = []
    for i in range(6):
        row = [
            str(i + 1),
            solution["Name"][i],
            solution["Cigar"][i],
            solution["MusicGenre"][i],
            solution["Drink"][i],
            solution["Mother"][i],
            solution["Food"][i],
        ]
        rows.append(row)
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False))