import json
from z3 import *

def main():
    solver = Solver()
    
    # Define variables for Names
    Alice = Int('Alice')
    Peter = Int('Peter')
    Bob = Int('Bob')
    Eric = Int('Eric')
    Arnold = Int('Arnold')
    names = {"Alice": Alice, "Peter": Peter, "Bob": Bob, "Eric": Eric, "Arnold": Arnold}
    
    # Define variables for Heights
    very_short = Int('very_short')
    short_h = Int('short')  # "short"
    tall_h = Int('tall')    # "tall"
    average_h = Int('average')  # "average"
    very_tall = Int('very_tall')
    heights = {"very short": very_short, "short": short_h, "tall": tall_h, "average": average_h, "very tall": very_tall}
    
    # Define variables for Mothers
    janelle = Int('janelle')
    kailyn = Int('kailyn')
    penny = Int('penny')
    holly = Int('holly')
    aniya = Int('aniya')
    mothers = {"Janelle": janelle, "Kailyn": kailyn, "Penny": penny, "Holly": holly, "Aniya": aniya}
    
    # Define variables for Hair Colors
    blonde = Int('blonde')
    black_hair = Int('black_hair')
    gray = Int('gray')
    red = Int('red')
    brown = Int('brown')
    hair = {"blonde": blonde, "black": black_hair, "gray": gray, "red": red, "brown": brown}
    
    # All variables range from 1 to 5 (houses)
    all_vars = list(names.values()) + list(heights.values()) + list(mothers.values()) + list(hair.values())
    for var in all_vars:
        solver.add(var >= 1, var <= 5)
    
    # All variables in the same category must be distinct.
    solver.add(Distinct(list(names.values())))
    solver.add(Distinct(list(heights.values())))
    solver.add(Distinct(list(mothers.values())))
    solver.add(Distinct(list(hair.values())))
    
    # Puzzle constraints based on the clues:
    # 1. The person who is tall is the person whose mother's name is Holly.
    solver.add(tall_h == holly)
    
    # 2. There are two houses between the person who has an average height and the person who is short.
    solver.add(Or(average_h - short_h == 3, short_h - average_h == 3))
    
    # 3. The person who has gray hair is directly left of the person whose mother's name is Janelle.
    solver.add(gray + 1 == janelle)
    
    # 4. The person who has black hair is not in the fourth house.
    solver.add(black_hair != 4)
    
    # 5. Eric is the person who has black hair.
    solver.add(Eric == black_hair)
    
    # 6. The person who is very short is the person whose mother's name is Penny.
    solver.add(very_short == penny)
    
    # 7. Eric and the person who has gray hair are next to each other.
    solver.add(Or(Eric - gray == 1, gray - Eric == 1))
    
    # 8. Bob is in the fifth house.
    solver.add(Bob == 5)
    
    # 9. The person who has red hair is Peter.
    solver.add(Peter == red)
    
    # 10. The person whose mother's name is Kailyn is directly left of the person who is short.
    solver.add(kailyn + 1 == short_h)
    
    # 11. Arnold is the person who has brown hair.
    solver.add(Arnold == brown)
    
    # 12. The person who has brown hair is somewhere to the left of the person whose mother's name is Janelle.
    solver.add(brown < janelle)
    
    # 13. The person whose mother's name is Aniya and the person who is very short are next to each other.
    solver.add(Or(aniya - very_short == 1, very_short - aniya == 1))
    
    # 14. The person whose mother's name is Kailyn is in the third house.
    solver.add(kailyn == 3)
    
    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        
        # Create reverse mappings: house number -> attribute
        house_to_name = {}
        for name, var in names.items():
            house_num = model.evaluate(var).as_long()
            house_to_name[house_num] = name
        
        house_to_height = {}
        for ht, var in heights.items():
            house_num = model.evaluate(var).as_long()
            house_to_height[house_num] = ht
        
        house_to_mother = {}
        for mother, var in mothers.items():
            house_num = model.evaluate(var).as_long()
            house_to_mother[house_num] = mother
        
        house_to_hair = {}
        for color, var in hair.items():
            house_num = model.evaluate(var).as_long()
            house_to_hair[house_num] = color
        
        # Build the solution dictionary in the required JSON structure.
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": []
            }
        }
        
        # Build rows for houses 1 to 5.
        for house in range(1, 6):
            row = [
                str(house),
                house_to_name[house],
                house_to_height[house],
                house_to_mother[house],
                house_to_hair[house]
            ]
            solution["solution"]["rows"].append(row)
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()