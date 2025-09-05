#!/usr/bin/env python3
import json
import sys

def solve():
    names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

    # assignment is a list of 6 houses; index 0 means house 1, etc.
    assignment = [None] * 6
    rem = {
        "Name": names[:],
        "HouseStyle": styles[:],
        "Food": foods[:],
        "Vacation": vacations[:],
        "Height": heights[:],
        "Cigar": cigars[:]
    }
    result = backtrack(0, assignment, rem)
    return result

def backtrack(i, assignment, rem):
    if i == 6:
        if valid(assignment):
            return assignment
        else:
            return None
    # Adjust available names based on fixed position:
    possible_names = rem["Name"][:]
    # House 5 (index 4) must be Alice.
    if i == 4:
        if "Alice" in possible_names:
            possible_names = ["Alice"]
        else:
            return None
    else:
        if "Alice" in possible_names:
            possible_names.remove("Alice")
    # House 4 (index 3) must be Eric.
    if i == 3:
        if "Eric" in possible_names:
            possible_names = ["Eric"]
        else:
            return None
    else:
        if "Eric" in possible_names:
            possible_names.remove("Eric")
    
    for name in possible_names:
        possible_styles = rem["HouseStyle"][:]
        if i == 4:
            if "victorian" in possible_styles:
                possible_styles = ["victorian"]
            else:
                continue
        # Modern houses must be to the left of house 5 (index 4)
        if i >= 4 and "modern" in possible_styles:
            possible_styles.remove("modern")
        # House 3 (index 2) cannot be Craftsman.
        if i == 2 and "craftsman" in possible_styles:
            possible_styles = [s for s in possible_styles if s != "craftsman"]
        for style in possible_styles:
            possible_foods = rem["Food"][:]
            if i == 4:
                if "spaghetti" in possible_foods:
                    possible_foods = ["spaghetti"]
                else:
                    continue
            for food in possible_foods:
                possible_vacations = rem["Vacation"][:]
                for vacation in possible_vacations:
                    possible_heights = rem["Height"][:]
                    for height in possible_heights:
                        possible_cigars = rem["Cigar"][:]
                        for cigar in possible_cigars:
                            candidate = {
                                "Name": name,
                                "HouseStyle": style,
                                "Food": food,
                                "Vacation": vacation,
                                "Height": height,
                                "Cigar": cigar
                            }
                            if not valid_house(candidate, i):
                                continue
                            assignment[i] = candidate
                            new_rem = {
                                "Name": rem["Name"][:],
                                "HouseStyle": rem["HouseStyle"][:],
                                "Food": rem["Food"][:],
                                "Vacation": rem["Vacation"][:],
                                "Height": rem["Height"][:],
                                "Cigar": rem["Cigar"][:]
                            }
                            try:
                                new_rem["Name"].remove(name)
                                new_rem["HouseStyle"].remove(style)
                                new_rem["Food"].remove(food)
                                new_rem["Vacation"].remove(vacation)
                                new_rem["Height"].remove(height)
                                new_rem["Cigar"].remove(cigar)
                            except ValueError:
                                continue
                            
                            if valid(assignment):
                                result = backtrack(i+1, assignment, new_rem)
                                if result is not None:
                                    return result
                            assignment[i] = None
    return None

def valid_house(candidate, pos):
    # Fixed assignments based on house number:
    if pos == 4:
        if candidate["Name"] != "Alice":
            return False
        if candidate["Food"] != "spaghetti":
            return False
        if candidate["HouseStyle"] != "victorian":
            return False
    if pos == 3:
        if candidate["Name"] != "Eric":
            return False
    if pos != 4 and candidate["Name"] == "Alice":
        return False
    if pos != 3 and candidate["Name"] == "Eric":
        return False

    # Stir fry <-> average and colonial
    if candidate["Food"] == "stir fry":
        if candidate["HouseStyle"] != "colonial":
            return False
        if candidate["Height"] != "average":
            return False
    if candidate["Height"] == "average":
        if candidate["Food"] != "stir fry":
            return False
        if candidate["HouseStyle"] != "colonial":
            return False

    # Arnold loves stew.
    if candidate["Name"] == "Arnold" and candidate["Food"] != "stew":
        return False

    # Mountain vacation <-> yellow monster and very tall.
    if candidate["Vacation"] == "mountain":
        if candidate["Cigar"] != "yellow monster":
            return False
        if candidate["Height"] != "very tall":
            return False
    if candidate["Cigar"] == "yellow monster":
        if candidate["Vacation"] != "mountain":
            return False
        if candidate["Height"] != "very tall":
            return False

    # Beach vacation <-> tall and ranch.
    if candidate["Vacation"] == "beach":
        if candidate["HouseStyle"] != "ranch":
            return False
        if candidate["Height"] != "tall":
            return False
    if candidate["Height"] == "tall":
        if candidate["Vacation"] != "beach":
            return False
        # Tall must be to the left of Victorian (house 5 at index 4)
        if pos >= 4:
            return False

    # Pizza <-> cultural
    if candidate["Food"] == "pizza" and candidate["Vacation"] != "cultural":
        return False
    if candidate["Vacation"] == "cultural" and candidate["Food"] != "pizza":
        return False

    # Spaghetti implies victorian
    if candidate["Food"] == "spaghetti" and candidate["HouseStyle"] != "victorian":
        return False

    # Modern houses only in positions left of house 5.
    if candidate["HouseStyle"] == "modern" and pos >= 4:
        return False

    # Ranch <-> Blue Master
    if candidate["HouseStyle"] == "ranch" and candidate["Cigar"] != "blue master":
        return False
    if candidate["Cigar"] == "blue master" and candidate["HouseStyle"] != "ranch":
        return False

    return True

def valid(assignment):
    n = len(assignment)
    # Check individual house conditions that involve neighbors (for already assigned houses)
    for i in range(n):
        if assignment[i] is not None:
            d = assignment[i]
            # Constraint: A house with height "short" must have a craftsman somewhere to its left.
            if d["Height"] == "short":
                found = False
                for j in range(i):
                    if assignment[j] is not None and assignment[j]["HouseStyle"] == "craftsman":
                        found = True
                        break
                if not found:
                    return False

    # Neighbor-based constraints (immediate neighbors)
    for i in range(n):
        if assignment[i] is not None:
            d = assignment[i]
            # (17) Stir fry immediately to the left of Bob.
            if d["Food"] == "stir fry":
                if i+1 < n and assignment[i+1] is not None:
                    if assignment[i+1]["Name"] != "Bob":
                        return False
            # (23) Blends immediately left of Blue Master.
            if d["Cigar"] == "blends":
                if i+1 < n and assignment[i+1] is not None:
                    if assignment[i+1]["Cigar"] != "blue master":
                        return False
            if d["Cigar"] == "blue master":
                if i-1 >= 0 and assignment[i-1] is not None:
                    if assignment[i-1]["Cigar"] != "blends":
                        return False
            # (13) Mountain vacation adjacent to Dunhill.
            if d["Vacation"] == "mountain":
                if i == 0 or i == n-1:
                    neighbor_idx = 1 if i == 0 else n-2
                    if assignment[neighbor_idx] is not None:
                        if assignment[neighbor_idx]["Cigar"] != "dunhill":
                            return False
                else:
                    if (assignment[i-1] is not None) and (assignment[i+1] is not None):
                        if assignment[i-1]["Cigar"] != "dunhill" and assignment[i+1]["Cigar"] != "dunhill":
                            return False
            if d["Cigar"] == "dunhill":
                if i == 0 or i == n-1:
                    neighbor_idx = 1 if i == 0 else n-2
                    if assignment[neighbor_idx] is not None:
                        if assignment[neighbor_idx]["Vacation"] != "mountain":
                            return False
                else:
                    if (assignment[i-1] is not None) and (assignment[i+1] is not None):
                        if assignment[i-1]["Vacation"] != "mountain" and assignment[i+1]["Vacation"] != "mountain":
                            return False

    # Pairwise constraints (when both houses are assigned)
    for i in range(n):
        for j in range(i+1, n):
            if assignment[i] is not None and assignment[j] is not None:
                d_i = assignment[i]
                d_j = assignment[j]
                # (5) The house with average (stir fry) and the house with Peter are 2 apart.
                if d_i["Height"] == "average" and d_j["Name"] == "Peter":
                    if abs(i - j) != 2:
                        return False
                if d_j["Height"] == "average" and d_i["Name"] == "Peter":
                    if abs(i - j) != 2:
                        return False
                # (10) Stir fry (colonial) and camping are 2 apart.
                if d_i["Food"] == "stir fry" and d_j["Vacation"] == "camping":
                    if abs(i - j) != 2:
                        return False
                if d_j["Food"] == "stir fry" and d_i["Vacation"] == "camping":
                    if abs(i - j) != 2:
                        return False
                # (20) Stir fry is to the left of the Prince smoker.
                if d_i["Food"] == "stir fry" and d_j["Cigar"] == "prince":
                    if i >= j:
                        return False
                if d_j["Food"] == "stir fry" and d_i["Cigar"] == "prince":
                    if j >= i:
                        return False
                # (21) Grilled cheese and super tall are 3 apart.
                if d_i["Food"] == "grilled cheese" and d_j["Height"] == "super tall":
                    if abs(i - j) != 3:
                        return False
                if d_j["Food"] == "grilled cheese" and d_i["Height"] == "super tall":
                    if abs(i - j) != 3:
                        return False
                # (25) Pizza is to the left of the cruise.
                if d_i["Food"] == "pizza" and d_j["Vacation"] == "cruise":
                    if i >= j:
                        return False
                if d_j["Food"] == "pizza" and d_i["Vacation"] == "cruise":
                    if j >= i:
                        return False
    return True

def main():
    sol = solve()
    if sol is None:
        result = {"solution": {"header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"], "rows": []}}
    else:
        rows = []
        for i, house in enumerate(sol):
            row = [str(i+1), house["Name"], house["HouseStyle"], house["Food"], house["Vacation"], house["Height"], house["Cigar"]]
            rows.append(row)
        result = {"solution": {"header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"], "rows": rows}}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()