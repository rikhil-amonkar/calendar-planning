import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks = ["milk", "root beer", "coffee", "tea", "water"]
    colors = ["blue", "green", "white", "yellow", "red"]
    flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

    # Initialize the houses with all possible values for each attribute
    houses = [{attr: set(values) for attr, values in zip(["Name", "Drink", "Color", "Flower", "Hobby"], 
                                                       [names, drinks, colors, flowers, hobbies])} for _ in range(5)]

    # Apply the constraints
    def apply_constraints(houses):
        # Constraint 1: Alice is not in the fourth house
        houses[3]["Name"].discard("Alice")

        # Constraint 2: The root beer lover is the person who enjoys gardening
        for i in range(5):
            if "root beer" in houses[i]["Drink"] and "gardening" in houses[i]["Hobby"]:
                houses[i]["Drink"] = {"root beer"}
                houses[i]["Hobby"] = {"gardening"}
            elif "root beer" in houses[i]["Drink"]:
                houses[i]["Hobby"] = {"gardening"}
            elif "gardening" in houses[i]["Hobby"]:
                houses[i]["Drink"] = {"root beer"}

        # Constraint 3: The person whose favorite color is green is the coffee drinker
        for i in range(5):
            if "green" in houses[i]["Color"] and "coffee" in houses[i]["Drink"]:
                houses[i]["Color"] = {"green"}
                houses[i]["Drink"] = {"coffee"}
            elif "green" in houses[i]["Color"]:
                houses[i]["Drink"] = {"coffee"}
            elif "coffee" in houses[i]["Drink"]:
                houses[i]["Color"] = {"green"}

        # Constraint 4: The person whose favorite color is green is the person who loves the bouquet of lilies
        for i in range(5):
            if "green" in houses[i]["Color"] and "lilies" in houses[i]["Flower"]:
                houses[i]["Color"] = {"green"}
                houses[i]["Flower"] = {"lilies"}
            elif "green" in houses[i]["Color"]:
                houses[i]["Flower"] = {"lilies"}
            elif "lilies" in houses[i]["Flower"]:
                houses[i]["Color"] = {"green"}

        # Constraint 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils
        for i in range(5):
            if "blue" in houses[i]["Color"]:
                for j in range(i):
                    houses[j]["Flower"].discard("daffodils")
            if "daffodils" in houses[i]["Flower"]:
                for j in range(i + 1, 5):
                    houses[j]["Color"].discard("blue")

        # Constraint 6: The person who loves cooking is the person who loves blue
        for i in range(5):
            if "cooking" in houses[i]["Hobby"] and "blue" in houses[i]["Color"]:
                houses[i]["Hobby"] = {"cooking"}
                houses[i]["Color"] = {"blue"}
            elif "cooking" in houses[i]["Hobby"]:
                houses[i]["Color"] = {"blue"}
            elif "blue" in houses[i]["Color"]:
                houses[i]["Hobby"] = {"cooking"}

        # Constraint 7: Eric is directly left of the tea drinker
        for i in range(4):
            if "Eric" in houses[i]["Name"] and "tea" in houses[i + 1]["Drink"]:
                houses[i]["Name"] = {"Eric"}
                houses[i + 1]["Drink"] = {"tea"}
            elif "Eric" in houses[i]["Name"]:
                houses[i + 1]["Drink"] = {"tea"}
            elif "tea" in houses[i + 1]["Drink"]:
                houses[i]["Name"] = {"Eric"}

        # Constraint 8: The one who only drinks water is Peter
        for i in range(5):
            if "Peter" in houses[i]["Name"] and "water" in houses[i]["Drink"]:
                houses[i]["Name"] = {"Peter"}
                houses[i]["Drink"] = {"water"}
            elif "Peter" in houses[i]["Name"]:
                houses[i]["Drink"] = {"water"}
            elif "water" in houses[i]["Drink"]:
                houses[i]["Name"] = {"Peter"}

        # Constraint 9: Arnold is the photography enthusiast
        for i in range(5):
            if "Arnold" in houses[i]["Name"] and "photography" in houses[i]["Hobby"]:
                houses[i]["Name"] = {"Arnold"}
                houses[i]["Hobby"] = {"photography"}
            elif "Arnold" in houses[i]["Name"]:
                houses[i]["Hobby"] = {"photography"}
            elif "photography" in houses[i]["Hobby"]:
                houses[i]["Name"] = {"Arnold"}

        # Constraint 10: The person who loves white is the person who loves the rose bouquet
        for i in range(5):
            if "white" in houses[i]["Color"] and "roses" in houses[i]["Flower"]:
                houses[i]["Color"] = {"white"}
                houses[i]["Flower"] = {"roses"}
            elif "white" in houses[i]["Color"]:
                houses[i]["Flower"] = {"roses"}
            elif "roses" in houses[i]["Flower"]:
                houses[i]["Color"] = {"white"}

        # Constraint 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red
        for i in range(4):
            if "carnations" in houses[i]["Flower"] and "red" in houses[i + 2]["Color"]:
                houses[i]["Flower"] = {"carnations"}
                houses[i + 2]["Color"] = {"red"}
            elif "carnations" in houses[i]["Flower"]:
                houses[i + 2]["Color"].discard("red")
            elif "red" in houses[i + 2]["Color"]:
                houses[i]["Flower"].discard("carnations")
        for i in range(1, 5):
            if "carnations" in houses[i]["Flower"] and "red" in houses[i - 2]["Color"]:
                houses[i]["Flower"] = {"carnations"}
                houses[i - 2]["Color"] = {"red"}
            elif "carnations" in houses[i]["Flower"]:
                houses[i - 2]["Color"].discard("red")
            elif "red" in houses[i - 2]["Color"]:
                houses[i]["Flower"].discard("carnations")

        # Constraint 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby
        for i in range(5):
            if "cooking" in houses[i]["Hobby"]:
                for j in range(i + 1, 5):
                    houses[j]["Hobby"].discard("painting")

        # Constraint 13: The one who only drinks water is in the third house
        houses[2]["Drink"] = {"water"}

        # Constraint 14: The person who loves a carnations arrangement is the root beer lover
        for i in range(5):
            if "carnations" in houses[i]["Flower"] and "root beer" in houses[i]["Drink"]:
                houses[i]["Flower"] = {"carnations"}
                houses[i]["Drink"] = {"root beer"}
            elif "carnations" in houses[i]["Flower"]:
                houses[i]["Drink"] = {"root beer"}
            elif "root beer" in houses[i]["Drink"]:
                houses[i]["Flower"] = {"carnations"}

        # Constraint 15: The person who loves white is in the second house
        houses[1]["Color"] = {"white"}

        return houses

    # Function to check if the current state is consistent
    def is_consistent(houses):
        for i in range(5):
            if len(houses[i]["Name"]) != 1 or len(houses[i]["Drink"]) != 1 or \
               len(houses[i]["Color"]) != 1 or len(houses[i]["Flower"]) != 1 or \
               len(houses[i]["Hobby"]) != 1:
                return False
        return True

    # Function to find the next variable to assign
    def select_unassigned_variable(houses):
        for i in range(5):
            for attr in ["Name", "Drink", "Color", "Flower", "Hobby"]:
                if len(houses[i][attr]) > 1:
                    return i, attr
        return None, None

    # Backtracking search function
    def backtrack(houses):
        if is_consistent(houses):
            return houses
        house_index, attr = select_unassigned_variable(houses)
        if house_index is None:
            return None
        original_values = houses[house_index][attr].copy()
        for value in original_values:
            houses[house_index][attr] = {value}
            new_houses = apply_constraints(houses.copy())
            result = backtrack(new_houses)
            if result is not None:
                return result
            houses[house_index][attr] = original_values
        return None

    # Solve the puzzle
    solved_houses = backtrack(apply_constraints(houses))

    # Format the solution as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": []
        }
    }

    for i in range(5):
        row = [str(i + 1)]
        for attr in ["Name", "Drink", "Color", "Flower", "Hobby"]:
            row.append(list(solved_houses[i][attr])[0])
        solution["solution"]["rows"].append(row)

    return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())