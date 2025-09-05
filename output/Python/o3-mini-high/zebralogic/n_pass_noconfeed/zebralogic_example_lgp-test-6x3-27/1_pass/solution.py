import itertools
import json

def main():
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    car_models = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    # Iterate over all permutations of names
    for name_perm in itertools.permutations(names):
        # Clue 6: Carol is somewhere to the right of Eric.
        if name_perm.index("Carol") <= name_perm.index("Eric"):
            continue
        # Clue 9: Carol is not in the sixth house.
        if name_perm[5] == "Carol":
            continue

        # Iterate over all permutations of occupations.
        for occ_perm in itertools.permutations(occupations):
            valid = True
            # Clue 7: The person who is a doctor is Eric.
            # Clue 10: The person who is an engineer is Bob.
            # Clue 14: Arnold is the person who is an artist.
            for i in range(6):
                if name_perm[i] == "Eric" and occ_perm[i] != "doctor":
                    valid = False
                    break
                if name_perm[i] == "Bob" and occ_perm[i] != "engineer":
                    valid = False
                    break
                if name_perm[i] == "Arnold" and occ_perm[i] != "artist":
                    valid = False
                    break
            if not valid:
                continue

            # Clue 5: The person who is a nurse is directly left of the person who is an artist.
            pos_artist = occ_perm.index("artist")
            if pos_artist == 0 or occ_perm[pos_artist - 1] != "nurse":
                continue

            # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
            if occ_perm.index("teacher") >= occ_perm.index("nurse"):
                continue

            # Clue 4: The person who is a lawyer is not in the fifth house.
            if occ_perm[4] == "lawyer":
                continue

            # Iterate over all permutations of car models.
            for car_perm in itertools.permutations(car_models):
                # Clue 1: The person who owns a Ford F-150 is in the fifth house.
                if car_perm[4] != "ford f150":
                    continue

                # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
                if car_perm[1] == "chevrolet silverado":
                    continue

                # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
                if car_perm.index("toyota camry") != occ_perm.index("nurse"):
                    continue

                # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
                if abs(car_perm.index("honda civic") - name_perm.index("Peter")) != 1:
                    continue

                # Clue 12: There is one house between Peter and the person who is a lawyer.
                if abs(name_perm.index("Peter") - occ_perm.index("lawyer")) != 2:
                    continue

                # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
                if abs(car_perm.index("tesla model 3") - name_perm.index("Bob")) != 2:
                    continue

                # If we reach here, all constraints are satisfied.
                solution_rows = []
                for i in range(6):
                    solution_rows.append([str(i + 1), name_perm[i], occ_perm[i], car_perm[i]])
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "CarModel"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(solution))
                return

if __name__ == "__main__":
    main()