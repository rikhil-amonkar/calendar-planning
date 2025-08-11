import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']

    # Initialize the solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": []
        }
    }

    # Generate all possible permutations for names, smoothies, nationalities
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for nationality_perm in permutations(nationalities):
                # Create a list of houses with their attributes
                assignment = []
                for i in range(5):
                    house = {
                        "House": str(i+1),
                        "Name": name_perm[i],
                        "Smoothie": smoothie_perm[i],
                        "Nationality": nationality_perm[i]
                    }
                    assignment.append(house)

                # Check all constraints
                # Constraint 2: Dragonfruit is in house 2
                if assignment[1]["Smoothie"] != "dragonfruit":
                    continue
                
                # Constraint 1: Dragonfruit is left of Eric
                eric_house = None
                dragonfruit_house = 2  # 0-based index 1 (house 2)
                for house in assignment:
                    if house["Name"] == "Eric":
                        eric_house = int(house["House"]) - 1
                        break
                if eric_house is None or dragonfruit_house >= eric_house:
                    continue
                
                # Constraint 3: Peter is not in house 1
                if assignment[0]["Name"] == "Peter":
                    continue
                
                # Constraint 4: Dane and Brit are next to each other
                dane_pos = None
                brit_pos = None
                for i in range(5):
                    if assignment[i]["Nationality"] == "dane":
                        dane_pos = i
                    if assignment[i]["Nationality"] == "brit":
                        brit_pos = i
                if dane_pos is None or brit_pos is None or abs(dane_pos - brit_pos) != 1:
                    continue
                
                # Constraint 5: Desert is not in house 5
                if assignment[4]["Smoothie"] == "desert":
                    continue
                
                # Constraint 6: Swede is left of Dragonfruit
                swede_pos = None
                for i in range(5):
                    if assignment[i]["Nationality"] == "swede":
                        swede_pos = i
                        break
                if swede_pos is None or swede_pos >= dragonfruit_house:
                    continue
                
                # Constraint 7: Two houses between Lime and Dane
                lime_pos = None
                for i in range(5):
                    if assignment[i]["Smoothie"] == "lime":
                        lime_pos = i
                        break
                if lime_pos is None or dane_pos is None or abs(lime_pos - dane_pos) != 3:
                    continue
                
                # Constraint 8: Bob is the Dane
                if assignment[dane_pos]["Name"] != "Bob":
                    continue
                
                # Constraint 9: Alice is Norwegian
                alice_pos = None
                for i in range(5):
                    if assignment[i]["Name"] == "Alice":
                        alice_pos = i
                        break
                if alice_pos is None or assignment[alice_pos]["Nationality"] != "norwegian":
                    continue
                
                # Constraint 10: Alice is in house 3
                if alice_pos != 2:  # 0-based index 2 is house 3
                    continue
                
                # Constraint 11: Watermelon is in house 3
                if assignment[2]["Smoothie"] != "watermelon":
                    continue
                
                # If all constraints are satisfied, build the solution
                rows = []
                for house in assignment:
                    rows.append([
                        house["House"],
                        house["Name"],
                        house["Smoothie"],
                        house["Nationality"]
                    ])
                solution["solution"]["rows"] = rows
                return solution

    return solution

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))