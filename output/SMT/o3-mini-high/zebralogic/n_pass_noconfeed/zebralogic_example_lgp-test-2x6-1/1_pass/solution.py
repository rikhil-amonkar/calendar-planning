from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 2

    # Create variables for each house and each attribute.
    # For each attribute, the possible values are 0 or 1.
    names = [Int(f"name_{i}") for i in range(num_houses)]
    sports = [Int(f"sport_{i}") for i in range(num_houses)]
    hair = [Int(f"hair_{i}") for i in range(num_houses)]
    heights = [Int(f"height_{i}") for i in range(num_houses)]
    smoothies = [Int(f"smoothie_{i}") for i in range(num_houses)]
    flowers = [Int(f"flower_{i}") for i in range(num_houses)]

    # Domain constraints: each variable is either 0 or 1.
    for var in names + sports + hair + heights + smoothies + flowers:
        solver.add(Or(var == 0, var == 1))

    # All-different constraints for each category.
    solver.add(Distinct(names))
    solver.add(Distinct(sports))
    solver.add(Distinct(hair))
    solver.add(Distinct(heights))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(flowers))

    # Mappings for each attribute:
    # Names:  0 -> "Arnold", 1 -> "Eric"
    # Sports: 0 -> "basketball", 1 -> "soccer"
    # Hair:   0 -> "brown", 1 -> "black"
    # Height: 0 -> "very short", 1 -> "short"
    # Smoothie: 0 -> "desert", 1 -> "cherry"
    # Flower: 0 -> "carnations", 1 -> "daffodils"
    
    # Clue 1: The person who loves soccer is not in the second house.
    # (sports value 1 stands for soccer; house index 1 is second house.)
    solver.add(sports[1] != 1)
    
    # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
    # In a 2-house puzzle, this forces house0 to have desert (0) and house1 to be very short (0).
    solver.add(smoothies[0] == 0)
    solver.add(heights[1] == 0)
    
    # Clue 3: The person who is very short is the person who has brown hair.
    # With our mapping, very short = 0 and brown hair = 0.
    # This clue makes the two attributes equivalent in each house.
    for i in range(num_houses):
        solver.add(heights[i] == hair[i])
    
    # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
    # With our mapping, desert = 0 and carnations = 0.
    # So for each house, the smoothie and flower values must be equivalent.
    for i in range(num_houses):
        solver.add(smoothies[i] == flowers[i])
    
    # Clue 5: Eric and the person who has brown hair are next to each other.
    # With our mapping, Eric = 1 and brown hair = 0.
    # In a 2-house puzzle, the only possible adjacent pair is house0 and house1.
    solver.add(Or(And(names[0] == 1, hair[1] == 0),
                  And(names[1] == 1, hair[0] == 0)))
    
    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        
        # Mapping dictionaries to convert integer values to their corresponding attributes.
        names_map = {0: "Arnold", 1: "Eric"}
        sports_map = {0: "basketball", 1: "soccer"}
        hair_map = {0: "brown", 1: "black"}
        height_map = {0: "very short", 1: "short"}
        smoothie_map = {0: "desert", 1: "cherry"}
        flower_map = {0: "carnations", 1: "daffodils"}
        
        header = ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"]
        rows = []
        for i in range(num_houses):
            house_number = str(i + 1)
            row = [
                house_number,
                names_map[model.evaluate(names[i]).as_long()],
                sports_map[model.evaluate(sports[i]).as_long()],
                hair_map[model.evaluate(hair[i]).as_long()],
                height_map[model.evaluate(heights[i]).as_long()],
                smoothie_map[model.evaluate(smoothies[i]).as_long()],
                flower_map[model.evaluate(flowers[i]).as_long()]
            ]
            rows.append(row)
        
        solution = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found."}))
        
if __name__ == "__main__":
    main()