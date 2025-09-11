import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays = ["april", "feb", "mar", "jan", "sept"]
    cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks = ["water", "coffee", "tea", "milk", "root beer"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(5)))

    for name_perm in permutations:
        for birthday_perm in permutations:
            for cigar_perm in permutations:
                for drink_perm in permutations:
                    # Create a dictionary to store the attributes of each house
                    house_attributes = {house: {"name": None, "birthday": None, "cigar": None, "drink": None} for house in houses}
                    
                    for i in range(5):
                        house_attributes[houses[i]]["name"] = names[name_perm[i]]
                        house_attributes[houses[i]]["birthday"] = birthdays[birthday_perm[i]]
                        house_attributes[houses[i]]["cigar"] = cigars[cigar_perm[i]]
                        house_attributes[houses[i]]["drink"] = drinks[drink_perm[i]]

                    # Check all clues
                    if (house_attributes[drink_perm[drinks.index("root beer")] + 1]["name"] == "Eric" and
                        house_attributes[2]["cigar"] == "pall mall" and
                        house_attributes[birthday_perm[birthdays.index("april")] + 1]["name"] == "Bob" and
                        house_attributes[birthday_perm[birthdays.index("mar")] + 1]["cigar"] == "dunhill" and
                        name_perm[names.index("Peter")] > drink_perm[drinks.index("root beer")] and
                        abs(name_perm[names.index("Peter")] - birthday_perm[birthdays.index("jan")]) == 1 and
                        birthday_perm[birthdays.index("feb")] == cigar_perm[cigars.index("blends")] and
                        birthday_perm[birthdays.index("feb")] == 1 and
                        name_perm[names.index("Arnold")] == name_perm[names.index("Peter")] and
                        drink_perm[drinks.index("milk")] != 3 and
                        cigar_perm[cigars.index("blue master")] + 1 == drink_perm[drinks.index("coffee")] + 1 and
                        abs(drink_perm[drinks.index("tea")] - drink_perm[drinks.index("coffee")]) == 2 and
                        name_perm[names.index("Eric")] == 2):
                        
                        # Construct the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                                "rows": []
                            }
                        }

                        for house in houses:
                            row = [
                                str(house),
                                house_attributes[house]["name"],
                                house_attributes[house]["birthday"],
                                house_attributes[house]["cigar"],
                                house_attributes[house]["drink"]
                            ]
                            solution["solution"]["rows"].append(row)

                        return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())