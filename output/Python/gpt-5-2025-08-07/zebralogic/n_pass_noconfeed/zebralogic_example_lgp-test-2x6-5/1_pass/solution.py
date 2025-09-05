import itertools
import json

def solve_puzzle():
    # Houses indexed 0..N-1 represent houses 1..N visually left-to-right
    N = 2
    houses = list(range(N))

    # Attributes
    Names = ["Arnold", "Eric"]
    Occupations = ["engineer", "doctor"]
    Birthdays = ["april", "sept"]
    HouseStyles = ["victorian", "colonial"]
    Heights = ["very short", "short"]
    Cigars = ["pall mall", "prince"]

    solutions = []

    # Helper to get index of a value in a permutation
    def idx(perm, value):
        return perm.index(value)

    for occ in itertools.permutations(Occupations):
        # Clue 1: The engineer is in the first house.
        if occ[0] != "engineer":
            continue

        for name in itertools.permutations(Names):
            # Clue 6: The engineer is Eric.
            if idx(name, "Eric") != idx(occ, "engineer"):
                continue

            for style in itertools.permutations(HouseStyles):
                # Clue 3: The colonial house is the engineer's house.
                if idx(style, "colonial") != idx(occ, "engineer"):
                    continue

                for height in itertools.permutations(Heights):
                    # Clue 4: The very short person is the engineer.
                    if idx(height, "very short") != idx(occ, "engineer"):
                        continue

                    for cigar in itertools.permutations(Cigars):
                        # Clue 5: The short person smokes Pall Mall.
                        if idx(height, "short") != idx(cigar, "pall mall"):
                            continue

                        for bday in itertools.permutations(Birthdays):
                            # Clue 2: April and the doctor are next to each other.
                            if abs(idx(bday, "april") - idx(occ, "doctor")) != 1:
                                continue

                            # All constraints satisfied; build solution rows
                            rows = []
                            for h in houses:
                                rows.append([
                                    str(h + 1),
                                    name[h],
                                    occ[h],
                                    bday[h],
                                    style[h],
                                    height[h],
                                    cigar[h],
                                ])
                            solutions.append(rows)

    if len(solutions) != 1:
        raise ValueError(f"Expected exactly one solution, found {len(solutions)}")

    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": solutions[0]
        }
    }
    return result


if __name__ == "__main__":
    print(json.dumps(solve_puzzle(), ensure_ascii=False))