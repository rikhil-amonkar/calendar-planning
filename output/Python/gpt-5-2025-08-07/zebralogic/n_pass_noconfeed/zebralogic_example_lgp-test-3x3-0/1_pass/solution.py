import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3]  # left (1) to right (3)
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    # Helper predicates
    def is_left_of(h1, h2):
        return h1 + 1 == h2

    def is_next_to(h1, h2):
        return abs(h1 - h2) == 1

    solutions = []

    # Permutations represent mapping from attribute value -> house number
    for name_perm in itertools.permutations(houses):
        house_of_name = dict(zip(names, name_perm))

        for edu_perm in itertools.permutations(houses):
            house_of_edu = dict(zip(educations, edu_perm))

            # Clue 3: Peter is the person with a high school diploma.
            if house_of_name["Peter"] != house_of_edu["high school"]:
                continue

            for occ_perm in itertools.permutations(houses):
                house_of_occ = dict(zip(occupations, occ_perm))

                # Clue 4: The person who is a doctor is the person with a bachelor's degree.
                if house_of_occ["doctor"] != house_of_edu["bachelor"]:
                    continue

                # Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
                if not is_left_of(house_of_occ["teacher"], house_of_edu["associate"]):
                    continue

                # Clue 2: The person with an associate's degree and Eric are next to each other.
                if not is_next_to(house_of_edu["associate"], house_of_name["Eric"]):
                    continue

                # Build reverse mappings: house -> attribute value
                name_at_house = {house_of_name[n]: n for n in names}
                edu_at_house = {house_of_edu[e]: e for e in educations}
                occ_at_house = {house_of_occ[o]: o for o in occupations}

                # Construct solution rows ordered by house number
                rows = []
                for h in houses:
                    rows.append([str(h), name_at_house[h], edu_at_house[h], occ_at_house[h]])

                solutions.append(rows)

    # Choose the first solution (expecting uniqueness)
    result_rows = solutions[0] if solutions else []

    output = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": result_rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))