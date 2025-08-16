from z3 import *
import json

def main():
    s = Solver()

    # Define the variables. Each attribute (name, occupation, car) gets a house number from 1 to 6.
    names = {
        "Alice": Int("Alice"),
        "Arnold": Int("Arnold"),
        "Eric": Int("Eric"),
        "Peter": Int("Peter"),
        "Bob": Int("Bob"),
        "Carol": Int("Carol")
    }
    
    occupations = {
        "engineer": Int("engineer"),
        "artist": Int("artist"),
        "doctor": Int("doctor"),
        "teacher": Int("teacher"),
        "nurse": Int("nurse"),
        "lawyer": Int("lawyer")
    }
    
    cars = {
        "chevrolet silverado": Int("chevrolet_silverado"),
        "ford f150": Int("ford_f150"),
        "honda civic": Int("honda_civic"),
        "toyota camry": Int("toyota_camry"),
        "bmw 3 series": Int("bmw_3_series"),
        "tesla model 3": Int("tesla_model_3")
    }

    # Domain: Each house number is between 1 and 6.
    all_vars = list(names.values()) + list(occupations.values()) + list(cars.values())
    for v in all_vars:
        s.add(And(v >= 1, v <= 6))

    # All-different constraints for each category.
    s.add(Distinct(list(names.values())))
    s.add(Distinct(list(occupations.values())))
    s.add(Distinct(list(cars.values())))

    # Clue 1: The person who owns a Ford F-150 is in the fifth house.
    s.add(cars["ford f150"] == 5)

    # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
    s.add(cars["chevrolet silverado"] != 2)

    # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
    s.add(Abs(cars["honda civic"] - names["Peter"]) == 1)

    # Clue 4: The person who is a lawyer is not in the fifth house.
    s.add(occupations["lawyer"] != 5)

    # Clue 5: The person who is a nurse is directly left of the person who is an artist.
    s.add(occupations["nurse"] + 1 == occupations["artist"])

    # Clue 6: Carol is somewhere to the right of Eric.
    s.add(names["Carol"] > names["Eric"])

    # Clue 7: The person who is a doctor is Eric.
    s.add(occupations["doctor"] == names["Eric"])

    # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
    s.add(occupations["teacher"] < occupations["nurse"])

    # Clue 9: Carol is not in the sixth house.
    s.add(names["Carol"] != 6)

    # Clue 10: The person who is an engineer is Bob.
    s.add(occupations["engineer"] == names["Bob"])

    # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
    s.add(cars["toyota camry"] == occupations["nurse"])

    # Clue 12: There is one house between Peter and the person who is a lawyer.
    s.add(Abs(names["Peter"] - occupations["lawyer"]) == 2)

    # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
    s.add(Abs(cars["tesla model 3"] - names["Bob"]) == 2)

    # Clue 14: Arnold is the person who is an artist.
    s.add(occupations["artist"] == names["Arnold"])

    # Check if the constraints are satisfiable and extract the model.
    if s.check() == sat:
        m = s.model()
        # Prepare the solution: list houses 1..6 in order.
        solution_rows = []
        for house in range(1, 7):
            # Identify the person (name) in this house.
            house_name = next(n for n in names if m.evaluate(names[n]).as_long() == house)
            # Identify the occupation in this house.
            house_occ = next(o for o in occupations if m.evaluate(occupations[o]).as_long() == house)
            # Identify the car model in this house.
            house_car = next(c for c in cars if m.evaluate(cars[c]).as_long() == house)
            
            solution_rows.append([str(house), house_name, house_occ, house_car])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        print("unsat")

if __name__ == "__main__":
    main()