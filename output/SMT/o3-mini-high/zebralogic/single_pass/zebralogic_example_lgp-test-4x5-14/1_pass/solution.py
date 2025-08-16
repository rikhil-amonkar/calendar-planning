from z3 import *
import json

def main():
    solver = Solver()
    houses = 4

    # For each house (index 0 to 3 corresponding to House 1 to 4)
    house_names = [Int(f"name_{i}") for i in range(houses)]
    house_mothers = [Int(f"mother_{i}") for i in range(houses)]
    house_smoothies = [Int(f"smoothie_{i}") for i in range(houses)]
    house_heights = [Int(f"height_{i}") for i in range(houses)]
    house_educations = [Int(f"education_{i}") for i in range(houses)]

    # Each attribute is a permutation of {1,2,3,4}. Constrain each variable to be in 1..4.
    for var in house_names + house_mothers + house_smoothies + house_heights + house_educations:
        solver.add(var >= 1, var <= 4)
    
    # All values in each category must be distinct.
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_mothers))
    solver.add(Distinct(house_smoothies))
    solver.add(Distinct(house_heights))
    solver.add(Distinct(house_educations))

    # We now set up our mappings (the numbers below are our chosen codes):
    # For Name: 1 = Peter, 2 = Alice, 3 = Eric, 4 = Arnold.
    # For Mother: 1 = Janelle, 2 = Holly, 3 = Aniya, 4 = Kailyn.
    # For Smoothie: 1 = watermelon, 2 = dragonfruit, 3 = desert, 4 = cherry.
    # For Height: 1 = tall, 2 = average, 3 = short, 4 = very short.
    # For Education: 1 = high school, 2 = associate, 3 = master, 4 = bachelor.

    # Clue 1: The person whose mother's name is Janelle is in the third house.
    # (House 3 is index 2; Janelle = 1)
    solver.add(house_mothers[2] == 1)

    # Clue 9: The person who is tall is the person whose mother's name is Janelle.
    # This means: for any house, if mother == Janelle (1) then height must be tall (1), and vice versa.
    for i in range(houses):
        solver.add(Implies(house_mothers[i] == 1, house_heights[i] == 1))
        solver.add(Implies(house_heights[i] == 1, house_mothers[i] == 1))

    # Clue 12: The person who is tall is Alice.
    # Since house with tall (height == 1) is unique, and by Clue 1 and 9 the third house is that person, force:
    solver.add(house_names[2] == 2)
    solver.add(house_heights[2] == 1)

    # Clue 2: The Desert smoothie lover is the person with a master's degree.
    # Desert = 3 and master = 3.
    for i in range(houses):
        solver.add(Implies(house_smoothies[i] == 3, house_educations[i] == 3))
    
    # Clue 3: The Desert smoothie lover is not in the first house.
    solver.add(house_smoothies[0] != 3)
    
    # Clue 4: The person who is very short is somewhere to the left of the person with a high school diploma.
    # Very short = 4; high school = 1.
    for i in range(houses):
        for j in range(houses):
            # For any houses i and j: if house i is very short and house j has high school then i must come before j.
            solver.add(Or(house_heights[i] != 4, house_educations[j] != 1, i < j))
    
    # Clue 5: Eric and the person who likes Cherry smoothies are next to each other.
    # Eric = 3 in our mapping; Cherry = 4.
    adjacent_conditions = []
    for i in range(houses - 1):
        cond = Or(And(house_names[i] == 3, house_smoothies[i+1] == 4),
                  And(house_names[i+1] == 3, house_smoothies[i] == 4))
        adjacent_conditions.append(cond)
    solver.add(Or(adjacent_conditions))
    
    # Clue 6: The person with a high school diploma is not in the third house.
    solver.add(house_educations[2] != 1)
    
    # Clue 7: The person whose mother's name is Kailyn is the person with an associate's degree.
    # Kailyn = 4, associate = 2.
    for i in range(houses):
        solver.add(Implies(house_mothers[i] == 4, house_educations[i] == 2))
        solver.add(Implies(house_educations[i] == 2, house_mothers[i] == 4))
    
    # Clue 8: The person who likes Cherry smoothies is the person whose mother's name is Aniya.
    # Cherry = 4, Aniya = 3.
    for i in range(houses):
        solver.add(Implies(house_smoothies[i] == 4, house_mothers[i] == 3))
        solver.add(Implies(house_mothers[i] == 3, house_smoothies[i] == 4))
    
    # Clue 10: Arnold is somewhere to the right of the person who has an average height.
    # Arnold = 4; average = 2.
    for i in range(houses):
        for j in range(houses):
            solver.add(Or(house_heights[i] != 2, house_names[j] != 4, i < j))
    
    # Clue 11: The Dragonfruit smoothie lover is directly left of the person who is short.
    # Dragonfruit = 2; short = 3.
    # That is, for some adjacent houses i and i+1, we must have house_smoothies[i]==2 and house_heights[i+1]==3.
    solver.add(Or([And(house_smoothies[i] == 2, house_heights[i+1] == 3) for i in range(houses - 1)]))
    
    # If the solver finds a solution, extract and decode it.
    if solver.check() == sat:
        m = solver.model()
        solution_rows = []
        # Decode using our mappings:
        name_map = {1: "Peter", 2: "Alice", 3: "Eric", 4: "Arnold"}
        mother_map = {1: "Janelle", 2: "Holly", 3: "Aniya", 4: "Kailyn"}
        smoothie_map = {1: "watermelon", 2: "dragonfruit", 3: "desert", 4: "cherry"}
        height_map = {1: "tall", 2: "average", 3: "short", 4: "very short"}
        education_map = {1: "high school", 2: "associate", 3: "master", 4: "bachelor"}
        
        for i in range(houses):
            house_no = str(i + 1)
            n_val = m[house_names[i]].as_long()
            mom_val = m[house_mothers[i]].as_long()
            sm_val = m[house_smoothies[i]].as_long()
            ht_val = m[house_heights[i]].as_long()
            edu_val = m[house_educations[i]].as_long()
            
            solution_rows.append([
                house_no,
                name_map[n_val],
                mother_map[mom_val],
                smoothie_map[sm_val],
                height_map[ht_val],
                education_map[edu_val]
            ])
        
        # Build the final output JSON dictionary.
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()