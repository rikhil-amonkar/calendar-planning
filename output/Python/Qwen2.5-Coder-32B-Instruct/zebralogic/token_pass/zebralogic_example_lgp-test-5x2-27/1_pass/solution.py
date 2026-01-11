import itertools
import json

# Define the possible values for names and heights
names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
heights = ["very tall", "average", "tall", "very short", "short"]

# Define the constraints as functions
def constraint1(house_names, house_heights):
    # The person who is short is in the second house.
    return house_heights[1] == "short"

def constraint2(house_names, house_heights):
    # Peter is directly left of Bob.
    for i in range(len(house_names) - 1):
        if house_names[i] == "Peter" and house_names[i + 1] == "Bob":
            return True
    return False

def constraint3(house_names, house_heights):
    # Eric is somewhere to the left of Peter.
    try:
        eric_index = house_names.index("Eric")
        peter_index = house_names.index("Peter")
        return eric_index < peter_index
    except ValueError:
        return False

def constraint4(house_names, house_heights):
    # The person who is very tall is directly left of Peter.
    for i in range(len(house_names) - 1):
        if house_heights[i] == "very tall" and house_names[i + 1] == "Peter":
            return True
    return False

def constraint5(house_names, house_heights):
    # Alice is directly left of the person who has an average height.
    for i in range(len(house_names) - 1):
        if house_names[i] == "Alice" and house_heights[i + 1] == "average":
            return True
    return False

def constraint6(house_names, house_heights):
    # The person who is short and the person who is very short are next to each other.
    short_index = house_heights.index("short")
    very_short_index = house_heights.index("very short")
    return abs(short_index - very_short_index) == 1

def constraint7(house_names, house_heights):
    # The person who has an average height is in the fifth house.
    return house_heights[-1] == "average"

# Function to check if a given arrangement satisfies all constraints
def check_constraints(house_names, house_heights):
    return (constraint1(house_names, house_heights) and
            constraint2(house_names, house_heights) and
            constraint3(house_names, house_heights) and
            constraint4(house_names, house_heights) and
            constraint5(house_names, house_heights) and
            constraint6(house_names, house_heights) and
            constraint7(house_names, house_heights))

# Generate all permutations of names and heights
for house_names in itertools.permutations(names):
    for house_heights in itertools.permutations(heights):
        if check_constraints(house_names, house_heights):
            # Format the solution as JSON
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": []
                }
            }
            for i in range(5):
                solution["solution"]["rows"].append([str(i + 1), house_names[i], house_heights[i]])
            
            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            break