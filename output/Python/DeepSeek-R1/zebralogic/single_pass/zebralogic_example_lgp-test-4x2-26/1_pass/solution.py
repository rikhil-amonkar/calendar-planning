import itertools
import json

def main():
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]
    houses = [1, 2, 3, 4]

    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            assignment = list(zip(name_perm, occ_perm))
            valid = True

            # Constraint 3: Peter not in first house
            if assignment[0][0] == "Peter":
                valid = False
                continue

            # Constraint 2: Teacher is Peter
            teacher_index = None
            for i, (name, occ) in enumerate(assignment):
                if occ == "teacher":
                    teacher_index = i
                    if name != "Peter":
                        valid = False
                    break

            if not valid or teacher_index is None:
                continue

            # Constraint 5: Artist is Alice
            artist_index = None
            for i, (name, occ) in enumerate(assignment):
                if occ == "artist":
                    artist_index = i
                    if name != "Alice":
                        valid = False
                    break

            if not valid or artist_index is None:
                continue

            # Build name to house mapping
            name_to_house = {name: idx + 1 for idx, (name, _) in enumerate(assignment)}

            # Constraint 1: Two houses between Eric and Peter
            if "Eric" not in name_to_house or "Peter" not in name_to_house:
                valid = False
            else:
                eric_house = name_to_house["Eric"]
                peter_house = name_to_house["Peter"]
                if abs(eric_house - peter_house) != 3:
                    valid = False

            if not valid:
                continue

            # Constraint 4: One house between doctor and Alice
            doctor_house = None
            for i, (_, occ) in enumerate(assignment):
                if occ == "doctor":
                    doctor_house = i + 1
                    break

            if doctor_house is None or "Alice" not in name_to_house:
                valid = False
            else:
                alice_house = name_to_house["Alice"]
                if abs(doctor_house - alice_house) != 2:
                    valid = False

            if valid:
                rows = []
                for i, (name, occ) in enumerate(assignment):
                    rows.append([str(i + 1), name, occ])
                
                result = {
                    "solution": {
                        "header": ["House", "Name", "Occupation"],
                        "rows": rows
                    }
                }
                print(json.dumps(result))
                return

    print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()