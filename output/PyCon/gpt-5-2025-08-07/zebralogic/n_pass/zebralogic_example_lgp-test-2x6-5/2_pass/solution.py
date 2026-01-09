import json
from itertools import product

def main():
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    occupations = ["engineer", "doctor"]
    birthdays = ["april", "sept"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    cigars = ["pall mall", "prince"]

    # Generate the two possible permutations for a two-value category
    def perms_2(vals):
        a, b = vals
        return [
            {a: 1, b: 2},
            {a: 2, b: 1}
        ]

    categories = {
        "Name": names,
        "Occupation": occupations,
        "Birthday": birthdays,
        "HouseStyle": house_styles,
        "Height": heights,
        "Cigar": cigars
    }

    all_perm_lists = {cat: perms_2(vals) for cat, vals in categories.items()}

    for name_map in all_perm_lists["Name"]:
        for occ_map in all_perm_lists["Occupation"]:
            # 1. The person who is an engineer is in the first house.
            if occ_map["engineer"] != 1:
                continue

            # 6. The person who is an engineer is Eric.
            if occ_map["engineer"] != name_map["Eric"]:
                continue

            for bday_map in all_perm_lists["Birthday"]:
                # 2. April and doctor are next to each other (with 2 houses: different).
                if abs(bday_map["april"] - occ_map["doctor"]) != 1:
                    continue

                for style_map in all_perm_lists["HouseStyle"]:
                    # 3. Colonial == engineer
                    if style_map["colonial"] != occ_map["engineer"]:
                        continue

                    for height_map in all_perm_lists["Height"]:
                        # 4. Very short == engineer
                        if height_map["very short"] != occ_map["engineer"]:
                            continue

                        for cigar_map in all_perm_lists["Cigar"]:
                            # 5. Short == Pall Mall
                            if height_map["short"] != cigar_map["pall mall"]:
                                continue

                            # Found a consistent solution
                            rows = []
                            for house in sorted(houses):
                                rows.append([
                                    str(house),
                                    next(v for v in names if name_map[v] == house),
                                    next(v for v in occupations if occ_map[v] == house),
                                    next(v for v in birthdays if bday_map[v] == house),
                                    next(v for v in house_styles if style_map[v] == house),
                                    next(v for v in heights if height_map[v] == house),
                                    next(v for v in cigars if cigar_map[v] == house),
                                ])

                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                                    "rows": rows
                                }
                            }
                            print(json.dumps(result, ensure_ascii=False))
                            return

    raise RuntimeError("No solution found")

if __name__ == "__main__":
    main()