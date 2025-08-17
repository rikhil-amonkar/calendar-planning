import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for height_perm in itertools.permutations(heights):
                for food_perm in itertools.permutations(foods):
                    # Create a dictionary to map house number to attributes
                    house_dict = {house: {"name": name, "hobby": hobby, "height": height, "food": food}
                                  for house, name, hobby, height, food in zip(houses, name_perm, hobby_perm, height_perm, food_perm)}

                    # Check all constraints
                    if (house_dict[house_dict["Bob"]["house"]]["hobby"] == "photography" and
                        house_dict[house_dict[next(h for h, d in house_dict.items() if d["food"] == "grilled cheese")]["house"]]["height"] == "tall" and
                        house_dict[2]["name"] != "Peter" and
                        house_dict[house_dict[next(h for h, d in house_dict.items() if d["food"] == "stir fry")]["house"] - 1]["height"] == "tall" and
                        house_dict[house_dict[next(h for h, d in house_dict.items() if d["hobby"] == "cooking")]["house"]]["height"] == "average" and
                        house_dict[house_dict["Alice"]["house"] + 1]["food"] == "pizza" and
                        house_dict[2]["food"] not in ["spaghetti"] and
                        house_dict[5]["name"] != "Eric" and
                        house_dict[house_dict["Peter"]["house"]]["height"] == "short" and
                        abs(house_dict[next(h for h, d in house_dict.items() if d["height"] == "average")]["house"] - house_dict[next(h for h, d in house_dict.items() if d["hobby"] == "gardening")]["house"]) == 1 and
                        house_dict[house_dict[next(h for h, d in house_dict.items() if d["hobby"] == "painting")]["house"] + 1] == house_dict[next(h for h, d in house_dict.items() if d["food"] == "grilled cheese")]["house"] and
                        house_dict[5]["height"] == "very short" and
                        house_dict[3]["height"] == "tall" and
                        house_dict["Alice"]["house"] > house_dict["Bob"]["house"]):
                        
                        # Prepare the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Hobby", "Height", "Food"],
                                "rows": [[str(house), data["name"], data["hobby"], data["height"], data["food"]] for house, data in house_dict.items()]
                            }
                        }
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())