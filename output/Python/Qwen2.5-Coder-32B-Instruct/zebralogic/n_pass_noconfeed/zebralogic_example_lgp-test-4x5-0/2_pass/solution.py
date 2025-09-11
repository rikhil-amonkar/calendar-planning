import itertools
import json

def find_house_by_attribute(house_dict, attribute, value):
    for house, attrs in house_dict.items():
        if attrs[attribute] == value:
            return house
    raise ValueError(f"No house found with {attribute} = {value}")

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3, 4]
    names = ["Eric", "Peter", "Arnold", "Alice"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    cigars = ["blue master", "pall mall", "dunhill", "prince"]
    heights = ["tall", "average", "short", "very short"]
    phones = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(houses))
    solutions = []

    # Iterate through all permutations and check constraints
    for perm_names in all_permutations:
        for perm_smoothies in all_permutations:
            for perm_cigars in all_permutations:
                for perm_heights in all_permutations:
                    for perm_phones in all_permutations:
                        # Create a dictionary to map each attribute to its value for each house
                        house_dict = {house: {} for house in houses}
                        for i, house in enumerate(houses):
                            house_dict[house]["Name"] = perm_names[i]
                            house_dict[house]["Smoothie"] = perm_smoothies[i]
                            house_dict[house]["Cigar"] = perm_cigars[i]
                            house_dict[house]["Height"] = perm_heights[i]
                            house_dict[house]["PhoneModel"] = perm_phones[i]

                        try:
                            # Check all constraints
                            if (house_dict[find_house_by_attribute(house_dict, "Smoothie", "dragonfruit")]["Name"] == "Eric" and
                                house_dict[find_house_by_attribute(house_dict, "Cigar", "dunhill")]["Smoothie"] == "cherry" and
                                find_house_by_attribute(house_dict, "PhoneModel", "samsung galaxy s21") + 1 ==
                                find_house_by_attribute(house_dict, "PhoneModel", "iphone 13") and
                                find_house_by_attribute(house_dict, "Cigar", "dunhill") >
                                find_house_by_attribute(house_dict, "Height", "very short") and
                                find_house_by_attribute(house_dict, "Smoothie", "watermelon") >
                                find_house_by_attribute(house_dict, "Smoothie", "desert") and
                                house_dict[find_house_by_attribute(house_dict, "Cigar", "prince")]["PhoneModel"] == "oneplus 9" and
                                house_dict[3]["Height"] == "tall" and
                                house_dict[find_house_by_attribute(house_dict, "PhoneModel", "iphone 13")]["Height"] == "very short" and
                                find_house_by_attribute(house_dict, "Cigar", "blue master") != 1 and
                                house_dict[find_house_by_attribute(house_dict, "Cigar", "dunhill")]["Height"] == "short" and
                                3 not in [house for house, attrs in house_dict.items() if attrs["Name"] == "Peter"] and
                                house_dict[find_house_by_attribute(house_dict, "PhoneModel", "google pixel 6")]["Name"] == "Arnold" and
                                house_dict[find_house_by_attribute(house_dict, "Smoothie", "dragonfruit")]["Cigar"] == "pall mall"):
                                
                                # If all constraints are satisfied, add to solutions
                                solutions.append(house_dict)
                        except ValueError:
                            continue

    # Convert the solution to the required JSON format
    if solutions:
        solution = solutions[0]  # Assuming there's only one valid solution
        rows = [[str(house), solution[house]["Name"], solution[house]["Smoothie"], solution[house]["Cigar"], solution[house]["Height"], solution[house]["PhoneModel"]] for house in houses]
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                "rows": rows
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"solution": {"header": [], "rows": []}})

# Run the solver and print the result
print(solve_puzzle())