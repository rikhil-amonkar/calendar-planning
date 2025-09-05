from z3 import Int, Solver, Distinct
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define houses positions: 1 to 4 for each unique attribute.
    houses = [1, 2, 3, 4]
    
    # Names
    names = ["Eric", "Alice", "Peter", "Arnold"]
    name_vars = {name: Int(name) for name in names}
    
    # Hair colors
    hair_colors = ["blonde", "black", "red", "brown"]
    hair_vars = {color: Int(color) for color in hair_colors}
    
    # Favorite sports
    sports = ["swimming", "soccer", "basketball", "tennis"]
    sport_vars = {sport: Int(sport) for sport in sports}
    
    # Add domain constraints (each variable must be between 1 and 4)
    for var in list(name_vars.values()) + list(hair_vars.values()) + list(sport_vars.values()):
        solver.add(var >= 1, var <= 4)
    
    # All values must be distinct within each category
    solver.add(Distinct(list(name_vars.values())))
    solver.add(Distinct(list(hair_vars.values())))
    solver.add(Distinct(list(sport_vars.values())))
    
    # Clue 1: The person who loves soccer is not in the second house.
    solver.add(sport_vars["soccer"] != 2)
    
    # Clue 2: Eric is the person who has blonde hair.
    solver.add(name_vars["Eric"] == hair_vars["blonde"])
    
    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    solver.add(hair_vars["blonde"] > sport_vars["basketball"])
    
    # Clue 4: The person who has black hair is the person who loves tennis.
    solver.add(hair_vars["black"] == sport_vars["tennis"])
    
    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    solver.add(name_vars["Arnold"] < hair_vars["red"])
    
    # Clue 6: Alice is the person who loves swimming.
    solver.add(name_vars["Alice"] == sport_vars["swimming"])
    
    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    solver.add(hair_vars["red"] + 1 == hair_vars["black"])
    
    # Solve the puzzle
    if solver.check() == "sat":
        model = solver.model()
        
        # Build inverse mapping: for each house number, determine name, hair color, sport.
        house_to_name = {}
        for name in names:
            pos = model.evaluate(name_vars[name]).as_long()
            house_to_name[pos] = name
        
        house_to_hair = {}
        for color in hair_colors:
            pos = model.evaluate(hair_vars[color]).as_long()
            house_to_hair[pos] = color
        
        house_to_sport = {}
        for sport in sports:
            pos = model.evaluate(sport_vars[sport]).as_long()
            house_to_sport[pos] = sport
        
        # Prepare rows in order from house 1 to 4
        rows = []
        for house in sorted(houses):
            row = [
                str(house),
                house_to_name.get(house, ""),
                house_to_hair.get(house, ""),
                house_to_sport.get(house, "")
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": []
            }
        }
        print(json.dumps(result))
        
if __name__ == "__main__":
    main()