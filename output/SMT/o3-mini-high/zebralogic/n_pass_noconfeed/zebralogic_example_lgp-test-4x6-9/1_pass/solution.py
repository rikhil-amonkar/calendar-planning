from z3 import *
import json

def main():
    # Domains indices:
    # Names: 0:Peter, 1:Arnold, 2:Eric, 3:Alice
    # Flowers: 0:daffodils, 1:carnations, 2:roses, 3:lilies
    # Heights: 0:very short, 1:short, 2:tall, 3:average
    # Mothers: 0:Janelle, 1:Kailyn, 2:Holly, 3:Aniya
    # Occupations: 0:engineer, 1:doctor, 2:teacher, 3:artist
    # Sports: 0:swimming, 1:basketball, 2:tennis, 3:soccer

    # Create 6 arrays for 4 houses
    num_houses = 4
    names   = [Int(f"name_{i}") for i in range(num_houses)]
    flowers = [Int(f"flower_{i}") for i in range(num_houses)]
    heights = [Int(f"height_{i}") for i in range(num_houses)]
    mothers = [Int(f"mother_{i}") for i in range(num_houses)]
    occupations = [Int(f"occupation_{i}") for i in range(num_houses)]
    sports = [Int(f"sport_{i}") for i in range(num_houses)]
    
    solver = Solver()
    
    # Domain constraints: each variable is between 0 and 3.
    for lst in [names, flowers, heights, mothers, occupations, sports]:
        for var in lst:
            solver.add(var >= 0, var <= 3)
    
    # All different constraints for each category.
    solver.add(Distinct(names))
    solver.add(Distinct(flowers))
    solver.add(Distinct(heights))
    solver.add(Distinct(mothers))
    solver.add(Distinct(occupations))
    solver.add(Distinct(sports))
    
    # Constant definitions for clarity
    Peter, Arnold, Eric, Alice = 0, 1, 2, 3
    daffodils, carnations, roses, lilies = 0, 1, 2, 3
    very_short, short, tall, average = 0, 1, 2, 3
    Janelle, Kailyn, Holly, Aniya = 0, 1, 2, 3
    engineer, doctor, teacher, artist = 0, 1, 2, 3
    swimming, basketball, tennis, soccer = 0, 1, 2, 3

    # Clue constraints applied for each house
    for i in range(num_houses):
        # Clues 1 & 2: The person who loves swimming is the same as the one who loves roses, and that person is Eric.
        solver.add(Implies(names[i] == Eric, And(flowers[i] == roses, sports[i] == swimming)))
        solver.add(Implies(flowers[i] == roses, names[i] == Eric))
        solver.add(Implies(sports[i] == swimming, flowers[i] == roses))
        
        # Clue 3 & 13: Arnold is tall and loves lilies.
        solver.add(Implies(names[i] == Arnold, And(heights[i] == tall, flowers[i] == lilies)))
        solver.add(Implies(heights[i] == tall, names[i] == Arnold))
        solver.add(Implies(flowers[i] == lilies, names[i] == Arnold))
        
        # Clue 5: The person who loves soccer is the person who is short.
        solver.add(Implies(sports[i] == soccer, heights[i] == short))
        solver.add(Implies(heights[i] == short, sports[i] == soccer))
        
        # Clue 7: The person whose mother's name is Janelle loves carnations.
        solver.add(Implies(mothers[i] == Janelle, flowers[i] == carnations))
        solver.add(Implies(flowers[i] == carnations, mothers[i] == Janelle))
        
        # Clue 8: The person who loves basketball is the person who has an average height.
        solver.add(Implies(sports[i] == basketball, heights[i] == average))
        solver.add(Implies(heights[i] == average, sports[i] == basketball))
        
        # Clue 11: Peter is the person who is a doctor.
        solver.add(Implies(names[i] == Peter, occupations[i] == doctor))
        solver.add(Implies(occupations[i] == doctor, names[i] == Peter))
        
        # Clue 12: The person whose mother's name is Aniya is Alice.
        solver.add(Implies(mothers[i] == Aniya, names[i] == Alice))
        solver.add(Implies(names[i] == Alice, mothers[i] == Aniya))
    
    # Clue 6: The teacher is in the first house.
    solver.add(occupations[0] == teacher)
    
    # Clue 9: Arnold is not in the third house (house index 2).
    solver.add(names[2] != Arnold)
    
    # Ordering constraints:
    # Clue 4: The person who loves daffodils (flower==daffodils) is somewhere to the right of the person who is an engineer.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(occupations[i] == engineer, flowers[j] == daffodils), i < j))
    
    # Clue 10: The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(mothers[i] == Holly, heights[j] == average), i > j))
    
    # Solve the puzzle.
    if solver.check() == sat:
        m = solver.model()
        # Mappings for output:
        names_map = ["Peter", "Arnold", "Eric", "Alice"]
        flowers_map = ["daffodils", "carnations", "roses", "lilies"]
        heights_map = ["very short", "short", "tall", "average"]
        mothers_map = ["Janelle", "Kailyn", "Holly", "Aniya"]
        occupations_map = ["engineer", "doctor", "teacher", "artist"]
        sports_map = ["swimming", "basketball", "tennis", "soccer"]
        
        # Build solution rows in order.
        rows = []
        for i in range(num_houses):
            house_num = str(i+1)
            row = [
                house_num,
                names_map[m.evaluate(names[i]).as_long()],
                flowers_map[m.evaluate(flowers[i]).as_long()],
                heights_map[m.evaluate(heights[i]).as_long()],
                mothers_map[m.evaluate(mothers[i]).as_long()],
                occupations_map[m.evaluate(occupations[i]).as_long()],
                sports_map[m.evaluate(sports[i]).as_long()]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == '__main__':
    main()