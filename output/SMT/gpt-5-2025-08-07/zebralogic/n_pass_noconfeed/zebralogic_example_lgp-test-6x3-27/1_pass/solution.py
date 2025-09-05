import json
from z3 import *

def main():
    # Define constants
    houses = range(6)  # 0..5 represent houses 1..6
    Names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    Occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    Cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    # Create variables: for each house, an index into the category list
    name_vars = [Int(f"name_{i}") for i in houses]
    occ_vars = [Int(f"occ_{i}") for i in houses]
    car_vars = [Int(f"car_{i}") for i in houses]

    s = Solver()

    # Domain constraints
    for i in houses:
        s.add(And(name_vars[i] >= 0, name_vars[i] < len(Names)))
        s.add(And(occ_vars[i] >= 0, occ_vars[i] < len(Occupations)))
        s.add(And(car_vars[i] >= 0, car_vars[i] < len(Cars)))

    # Uniqueness: each value appears exactly once across houses (per category)
    s.add(Distinct(name_vars))
    s.add(Distinct(occ_vars))
    s.add(Distinct(car_vars))

    # Helper to get index
    def idx(lst, val):
        return lst.index(val)

    # Position variables for referenced attributes and linking constraints
    def pos_var(name):
        return Int(name)

    # Link a position variable to a specific value in an attribute array
    def link_pos(attr_array, value_index, pos):
        # pos in [0,5]
        s.add(And(pos >= 0, pos < 6))
        # If house i has the value, then pos == i
        for i in houses:
            s.add(Implies(attr_array[i] == value_index, pos == i))

    # Create position variables for needed references
    pos_name = {
        "Peter": pos_var("pos_name_Peter"),
        "Carol": pos_var("pos_name_Carol"),
        "Eric": pos_var("pos_name_Eric"),
        "Bob": pos_var("pos_name_Bob"),
        "Arnold": pos_var("pos_name_Arnold"),
    }
    pos_occ = {
        "lawyer": pos_var("pos_occ_lawyer"),
        "nurse": pos_var("pos_occ_nurse"),
        "artist": pos_var("pos_occ_artist"),
        "teacher": pos_var("pos_occ_teacher"),
        "doctor": pos_var("pos_occ_doctor"),
        "engineer": pos_var("pos_occ_engineer"),
    }
    pos_car = {
        "honda civic": pos_var("pos_car_honda_civic"),
        "toyota camry": pos_var("pos_car_toyota_camry"),
        "tesla model 3": pos_var("pos_car_tesla_model_3"),
    }

    # Link positions to arrays
    for key, pv in pos_name.items():
        link_pos(name_vars, idx(Names, key), pv)
    for key, pv in pos_occ.items():
        link_pos(occ_vars, idx(Occupations, key), pv)
    for key, pv in pos_car.items():
        link_pos(car_vars, idx(Cars, key), pv)

    # Clues as constraints
    # 1. The person who owns a Ford F-150 is in the fifth house.
    s.add(car_vars[4] == idx(Cars, "ford f150"))

    # 2. The person who owns a Chevrolet Silverado is not in the second house.
    s.add(car_vars[1] != idx(Cars, "chevrolet silverado"))

    # 3. The person who owns a Honda Civic and Peter are next to each other.
    s.add(Abs(pos_car["honda civic"] - pos_name["Peter"]) == 1)

    # 4. The person who is a lawyer is not in the fifth house.
    s.add(occ_vars[4] != idx(Occupations, "lawyer"))

    # 5. The person who is a nurse is directly left of the person who is an artist.
    s.add(pos_occ["artist"] == pos_occ["nurse"] + 1)

    # 6. Carol is somewhere to the right of Eric.
    s.add(pos_name["Carol"] > pos_name["Eric"])

    # 7. The person who is a doctor is Eric.
    s.add(pos_occ["doctor"] == pos_name["Eric"])

    # 8. The person who is a teacher is somewhere to the left of the person who is a nurse.
    s.add(pos_occ["teacher"] < pos_occ["nurse"])

    # 9. Carol is not in the sixth house.
    s.add(name_vars[5] != idx(Names, "Carol"))

    # 10. The person who is an engineer is Bob.
    s.add(pos_occ["engineer"] == pos_name["Bob"])

    # 11. The person who owns a Toyota Camry is the person who is a nurse.
    s.add(pos_car["toyota camry"] == pos_occ["nurse"])

    # 12. There is one house between Peter and the person who is a lawyer.
    s.add(Abs(pos_name["Peter"] - pos_occ["lawyer"]) == 2)

    # 13. There is one house between the person who owns a Tesla Model 3 and Bob.
    s.add(Abs(pos_car["tesla model 3"] - pos_name["Bob"]) == 2)

    # 14. Arnold is the person who is an artist.
    s.add(pos_name["Arnold"] == pos_occ["artist"])

    # Solve
    if s.check() != sat:
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Build output rows
    rows = []
    for i in houses:
        house_num = str(i + 1)
        name_val = Names[m.evaluate(name_vars[i]).as_long()]
        occ_val = Occupations[m.evaluate(occ_vars[i]).as_long()]
        car_val = Cars[m.evaluate(car_vars[i]).as_long()]
        rows.append([house_num, name_val, occ_val, car_val])

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()