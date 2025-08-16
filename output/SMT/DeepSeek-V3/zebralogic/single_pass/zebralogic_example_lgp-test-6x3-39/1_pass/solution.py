from z3 import *

def solve_housing_problem():
    # Initialize the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the attributes
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Create variables for each attribute in each house
    name_vars = {house: Int(f"name_{house}") for house in houses}
    child_vars = {house: Int(f"child_{house}") for house in houses}
    smoothie_vars = {house: Int(f"smoothie_{house}") for house in houses}

    # Add constraints that each attribute is within the valid range (0 to 5 for the indices)
    for house in houses:
        s.add(name_vars[house] >= 0, name_vars[house] < len(names))
        s.add(child_vars[house] >= 0, child_vars[house] < len(children))
        s.add(smoothie_vars[house] >= 0, smoothie_vars[house] < len(smoothies))

    # Each attribute must be unique across houses
    s.add(Distinct([name_vars[house] for house in houses]))
    s.add(Distinct([child_vars[house] for house in houses]))
    s.add(Distinct([smoothie_vars[house] for house in houses]))

    # Clue 6: Alice is the person whose child is named Alice.
    # This means that in the house where the name is Alice, the child is Alice.
    for house in houses:
        s.add(Implies(name_vars[house] == names.index("Alice"), child_vars[house] == children.index("Alice")))

    # Clue 7: Alice is the Watermelon smoothie lover.
    for house in houses:
        s.add(Implies(name_vars[house] == names.index("Alice"), smoothie_vars[house] == smoothies.index("watermelon")))

    # Clue 10: Bob is the mother of Timothy.
    for house in houses:
        s.add(Implies(name_vars[house] == names.index("Bob"), child_vars[house] == children.index("Timothy")))

    # Clue 11: Arnold is directly left of Carol.
    # This means Arnold is in house n and Carol is in house n+1.
    for i in range(1, 6):
        s.add(Implies(name_vars[i] == names.index("Arnold"), name_vars[i+1] == names.index("Carol")))
    # Also, Arnold cannot be in house 6
    s.add(name_vars[6] != names.index("Arnold"))

    # Clue 13: The person whose child is named Meredith is in the sixth house.
    s.add(child_vars[6] == children.index("Meredith"))

    # Clue 14: The Dragonfruit smoothie lover is the person whose child is named Meredith.
    s.add(smoothie_vars[6] == smoothies.index("dragonfruit"))

    # Clue 3: Alice is not in the fifth house.
    s.add(name_vars[5] != names.index("Alice"))

    # Clue 4: The person whose child is named Samantha is not in the second house.
    s.add(child_vars[2] != children.index("Samantha"))

    # Clue 9: Arnold is not in the second house.
    s.add(name_vars[2] != names.index("Arnold"))

    # Clue 8: Peter is somewhere to the right of the person whose child is named Samantha.
    # First, find the house where child is Samantha, then Peter must be in a house with higher number.
    # We need to express that for all houses, if the child is Samantha, then Peter is in a house to the right.
    for samantha_house in houses:
        for peter_house in houses:
            if peter_house > samantha_house:
                s.add(Implies(child_vars[samantha_house] == children.index("Samantha"), name_vars[peter_house] == names.index("Peter")))

    # Clue 12: The person who likes Cherry smoothies is directly left of the person whose child is named Samantha.
    # So cherry is in house n, Samantha is in house n+1.
    for i in range(1, 6):
        s.add(Implies(smoothie_vars[i] == smoothies.index("cherry"), child_vars[i+1] == children.index("Samantha"))

    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
    # So cherry is in house n, watermelon is in house m where m > n.
    for cherry_house in houses:
        for watermelon_house in houses:
            if watermelon_house > cherry_house:
                s.add(Implies(smoothie_vars[cherry_house] == smoothies.index("cherry"), smoothie_vars[watermelon_house] == smoothies.index("watermelon")))

    # Clue 2: The person who drinks Blueberry smoothies is somewhere to the left of the person whose child is named Fred.
    # So blueberry is in house n, Fred is in house m where m > n.
    for blueberry_house in houses:
        for fred_house in houses:
            if fred_house > blueberry_house:
                s.add(Implies(smoothie_vars[blueberry_house] == smoothies.index("blueberry"), child_vars[fred_house] == children.index("Fred")))

    # Clue 1: The person whose child is named Fred and the Desert smoothie lover are next to each other.
    # So either Fred is in n and desert in n+1, or desert in n and Fred in n+1.
    for i in range(1, 6):
        s.add(Or(
            And(child_vars[i] == children.index("Fred"), smoothie_vars[i+1] == smoothies.index("desert")),
            And(smoothie_vars[i] == smoothies.index("desert"), child_vars[i+1] == children.index("Fred"))
        ))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": []}}
        
        for house in sorted(houses):
            name_idx = model.evaluate(name_vars[house]).as_long()
            child_idx = model.evaluate(child_vars[house]).as_long()
            smoothie_idx = model.evaluate(smoothie_vars[house]).as_long()
            
            solution["solution"]["rows"].append([
                str(house),
                names[name_idx],
                children[child_idx],
                smoothies[smoothie_idx]
            ])
        
        return solution
    else:
        return {"error": "No solution found"}

# Print the solution in JSON format
import json
print(json.dumps(solve_housing_problem(), indent=2))