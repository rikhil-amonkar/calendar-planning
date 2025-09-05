from z3 import *
import json

def main():
    num_houses = 2
    houses = []
    for i in range(num_houses):
        house = {}
        house["name"] = Int(f"name_{i}")
        house["education"] = Int(f"education_{i}")
        house["height"] = Int(f"height_{i}")
        house["food"] = Int(f"food_{i}")
        house["drink"] = Int(f"drink_{i}")
        houses.append(house)

    s = Solver()

    # Each attribute variable can only be 0 or 1.
    # Mappings:
    # Name: 0 = "Arnold", 1 = "Eric"
    # Education: 0 = "associate", 1 = "high school"
    # Height: 0 = "short", 1 = "very short"
    # Food: 0 = "grilled cheese", 1 = "pizza"
    # Drink: 0 = "tea", 1 = "water"
    for house in houses:
        s.add(Or(house["name"] == 0, house["name"] == 1))
        s.add(Or(house["education"] == 0, house["education"] == 1))
        s.add(Or(house["height"] == 0, house["height"] == 1))
        s.add(Or(house["food"] == 0, house["food"] == 1))
        s.add(Or(house["drink"] == 0, house["drink"] == 1))

    # Uniqueness: All houses must have distinct values for each attribute.
    s.add(Distinct([house["name"] for house in houses]))
    s.add(Distinct([house["education"] for house in houses]))
    s.add(Distinct([house["height"] for house in houses]))
    s.add(Distinct([house["food"] for house in houses]))
    s.add(Distinct([house["drink"] for house in houses]))

    # Clue 1: The person who is very short is the person who is a pizza lover.
    # (i.e., Height 1 <=> Food 1)
    for house in houses:
        s.add(house["height"] == house["food"])

    # Clue 2: The person who loves eating grilled cheese is in the second house.
    # (i.e., in house 2, Food must be 0, which means grilled cheese.)
    s.add(houses[1]["food"] == 0)

    # Clue 3: The person with a high school diploma is the person who is a pizza lover.
    # (i.e., Education 1 <=> Food 1)
    for house in houses:
        s.add(house["education"] == house["food"])

    # Clue 4: The tea drinker is the person who loves eating grilled cheese.
    # (i.e., Drink 0 <=> Food 0)
    for house in houses:
        s.add(house["drink"] == house["food"])

    # Clue 5: Arnold is the person who is a pizza lover.
    # (i.e., if Name is 0 (Arnold) then Food must be 1 (pizza))
    for house in houses:
        s.add(Implies(house["name"] == 0, house["food"] == 1))

    if s.check() == sat:
        m = s.model()
        name_map = {0: "Arnold", 1: "Eric"}
        education_map = {0: "associate", 1: "high school"}
        height_map = {0: "short", 1: "very short"}
        food_map = {0: "grilled cheese", 1: "pizza"}
        drink_map = {0: "tea", 1: "water"}

        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": []
            }
        }
        # Houses are ordered: House 1 is index 0, House 2 is index 1.
        for i, house in enumerate(houses):
            house_num = str(i+1)
            name_val = name_map[m[house["name"]].as_long()]
            edu_val = education_map[m[house["education"]].as_long()]
            height_val = height_map[m[house["height"]].as_long()]
            food_val = food_map[m[house["food"]].as_long()]
            drink_val = drink_map[m[house["drink"]].as_long()]
            solution["solution"]["rows"].append(
                [house_num, name_val, edu_val, height_val, food_val, drink_val]
            )
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()