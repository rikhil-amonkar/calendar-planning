import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]

    # Generate all possible permutations
    for name_order in itertools.permutations(names):
        for smoothie_order in itertools.permutations(smoothies):
            for nationality_order in itertools.permutations(nationalities):
                # Create a dictionary to store the attributes of each house
                house_attributes = {house: {} for house in houses}
                
                for i in range(5):
                    house_attributes[houses[i]]["Name"] = name_order[i]
                    house_attributes[houses[i]]["Smoothie"] = smoothie_order[i]
                    house_attributes[houses[i]]["Nationality"] = nationality_order[i]

                # Check all constraints
                if (smoothie_order.index("dragonfruit") < name_order.index("Eric") and
                    smoothie_order[1] == "dragonfruit" and
                    name_order[0] != "Peter" and
                    abs(nationality_order.index("dane") - nationality_order.index("brit")) == 1 and
                    smoothie_order[4] != "desert" and
                    nationality_order.index("swede") < smoothie_order.index("dragonfruit") and
                    abs(smoothie_order.index("lime") - nationality_order.index("dane")) == 3 and
                    nationality_order[name_order.index("Bob")] == "dane" and
                    nationality_order[name_order.index("Alice")] == "norwegian" and
                    name_order[2] == "Alice" and
                    smoothie_order[2] == "watermelon"):
                    
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Nationality"],
                            "rows": []
                        }
                    }
                    
                    for house in houses:
                        row = [str(house), house_attributes[house]["Name"], house_attributes[house]["Smoothie"], house_attributes[house]["Nationality"]]
                        solution["solution"]["rows"].append(row)
                    
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())