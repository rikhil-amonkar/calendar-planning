from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute
house_names = [Int(f"house_name_{i}") for i in range(1, 3)]
house_children = [Int(f"house_child_{i}") for i in range(1, 3)]
house_food = [Int(f"house_food_{i}") for i in range(1, 3)]

# Define domains for each variable
names = {"Eric": 0, "Arnold": 1}
children = {"Bella": 0, "Fred": 1}
food = {"grilled cheese": 0, "pizza": 1}

# Constraints for unique values in each category
solver.add(Distinct(house_names))
solver.add(Distinct(house_children))
solver.add(Distinct(house_food))

# Clue 1: The person who is a pizza lover is Arnold.
solver.add(house_food[1] == food["pizza"] | house_food[0] == food["pizza"])
solver.add((house_food[1] == food["pizza"]) == (house_names[1] == names["Arnold"]) |
           (house_food[0] == food["pizza"]) == (house_names[0] == names["Arnold"]))

# Clue 2: The person who loves eating grilled cheese is directly left of the person whose child is named Fred.
solver.add((house_food[0] == food["grilled cheese"]) & (house_children[1] == children["Fred"]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution_house1_name = [k for k, v in names.items() if v == model[house_names[0]].as_long()][0]
    solution_house1_child = [k for k, v in children.items() if v == model[house_children[0]].as_long()][0]
    solution_house1_food = [k for k, v in food.items() if v == model[house_food[0]].as_long()][0]
    
    solution_house2_name = [k for k, v in names.items() if v == model[house_names[1]].as_long()][0]
    solution_house2_child = [k for k, v in children.items() if v == model[house_children[1]].as_long()][0]
    solution_house2_food = [k for k, v in food.items() if v == model[house_food[1]].as_long()][0]
    
    # Format the solution as required
    solution = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": [
                ["1", solution_house1_name, solution_house1_child, solution_house1_food],
                ["2", solution_house2_name, solution_house2_child, solution_house2_food]
            ]
        }
    }
    
    print(solution)
else:
    print("No solution found")