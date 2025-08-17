import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    phones = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    colors = ["blue", "red", "yellow", "green", "white", "purple"]

    for name_order in itertools.permutations(names):
        if name_order[2] != "Carol" and abs(name_order.index("Dane") - name_order.index("brit")) == 2 and name_order[name_order.index("Carol")] == "green":
            for phone_order in itertools.permutations(phones):
                if phone_order[4] == "samsung galaxy s21" and phone_order[phone_order.index("oneplus 9")] == "purple" and phone_order[2] != "huawei p50" and phone_order[4] == "samsung galaxy s21" and name_order[phone_order.index("samsung galaxy s21")] == "Bob" and phone_order.index("samsung galaxy s21") < name_order.index("Peter") and phone_order[4] == "samsung galaxy s21" and phone_order[4 + 1] == "iphone 13":
                    for nationality_order in itertools.permutations(nationalities):
                        if nationality_order[name_order.index("Alice")] == "german" and nationality_order[name_order.index("Dane")] == "yellow" and nationality_order[name_order.index("Peter")] == "brit" and nationality_order[name_order.index("Norwegian")] == "purple" and nationality_order[name_order.index("Chinese")] == "xiaomi mi 11":
                            for color_order in itertools.permutations(colors):
                                if color_order[name_order.index("Carol")] == "green" and color_order[name_order.index("Dane")] == "yellow" and color_order[name_order.index("Peter")] == "blue" and color_order.index("white") > color_order.index("red"):
                                    if name_order.index("Arnold") + 1 == name_order.index("Alice"):
                                        solution = {
                                            "solution": {
                                                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                                                "rows": [
                                                    [str(houses[i]), name_order[i], phone_order[i], nationality_order[i], color_order[i]] for i in range(6)
                                                ]
                                            }
                                        }
                                        return json.dumps(solution, indent=2)

print(solve_puzzle())