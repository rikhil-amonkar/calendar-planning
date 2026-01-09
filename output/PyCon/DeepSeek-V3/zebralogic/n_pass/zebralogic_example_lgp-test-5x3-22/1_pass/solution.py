import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: house numbers 1-5
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for each attribute
    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]
    
    # Add variables for each house
    problem.addVariables(["name"], names)
    problem.addVariables(["smoothie"], smoothies)
    problem.addVariables(["nationality"], nationalities)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ["name"])
    problem.addConstraint(AllDifferentConstraint(), ["smoothie"])
    problem.addConstraint(AllDifferentConstraint(), ["nationality"])
    
    # Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric
    def dragonfruit_left_of_eric(name_vars, smoothie_vars):
        dragonfruit_house = None
        eric_house = None
        for house in houses:
            if smoothie_vars[house] == "dragonfruit":
                dragonfruit_house = house
            if name_vars[house] == "Eric":
                eric_house = house
        return dragonfruit_house < eric_house
    
    # Clue 2: The Dragonfruit smoothie lover is in the second house
    def dragonfruit_second(smoothie_vars):
        return smoothie_vars[2] == "dragonfruit"
    
    # Clue 3: Peter is not in the first house
    def peter_not_first(name_vars):
        return name_vars[1] != "Peter"
    
    # Clue 4: The Dane and the British person are next to each other
    def dane_brit_adjacent(nationality_vars):
        dane_house = None
        brit_house = None
        for house in houses:
            if nationality_vars[house] == "dane":
                dane_house = house
            if nationality_vars[house] == "brit":
                brit_house = house
        return abs(dane_house - brit_house) == 1
    
    # Clue 5: The Desert smoothie lover is not in the fifth house
    def desert_not_fifth(smoothie_vars):
        return smoothie_vars[5] != "desert"
    
    # Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover
    def swede_left_of_dragonfruit(nationality_vars, smoothie_vars):
        swede_house = None
        dragonfruit_house = None
        for house in houses:
            if nationality_vars[house] == "swede":
                swede_house = house
            if smoothie_vars[house] == "dragonfruit":
                dragonfruit_house = house
        return swede_house < dragonfruit_house
    
    # Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane
    def lime_dane_two_houses(smoothie_vars, nationality_vars):
        lime_house = None
        dane_house = None
        for house in houses:
            if smoothie_vars[house] == "lime":
                lime_house = house
            if nationality_vars[house] == "dane":
                dane_house = house
        return abs(lime_house - dane_house) == 3
    
    # Clue 8: Bob is the Dane
    def bob_is_dane(name_vars, nationality_vars):
        for house in houses:
            if name_vars[house] == "Bob":
                return nationality_vars[house] == "dane"
        return False
    
    # Clue 9: Alice is the Norwegian
    def alice_is_norwegian(name_vars, nationality_vars):
        for house in houses:
            if name_vars[house] == "Alice":
                return nationality_vars[house] == "norwegian"
        return False
    
    # Clue 10: Alice is in the third house
    def alice_third(name_vars):
        return name_vars[3] == "Alice"
    
    # Clue 11: The Watermelon smoothie lover is in the third house
    def watermelon_third(smoothie_vars):
        return smoothie_vars[3] == "watermelon"
    
    # Add all constraints
    problem.addConstraint(dragonfruit_left_of_eric, ["name", "smoothie"])
    problem.addConstraint(dragonfruit_second, ["smoothie"])
    problem.addConstraint(peter_not_first, ["name"])
    problem.addConstraint(dane_brit_adjacent, ["nationality"])
    problem.addConstraint(desert_not_fifth, ["smoothie"])
    problem.addConstraint(swede_left_of_dragonfruit, ["nationality", "smoothie"])
    problem.addConstraint(lime_dane_two_houses, ["smoothie", "nationality"])
    problem.addConstraint(bob_is_dane, ["name", "nationality"])
    problem.addConstraint(alice_is_norwegian, ["name", "nationality"])
    problem.addConstraint(alice_third, ["name"])
    problem.addConstraint(watermelon_third, ["smoothie"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Smoothie", "Nationality"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    
    rows = []
    for house in sorted(houses):
        name = solution.get(("name", house))
        smoothie = solution.get(("smoothie", house))
        nationality = solution.get(("nationality", house))
        rows.append([str(house), name, smoothie, nationality])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))