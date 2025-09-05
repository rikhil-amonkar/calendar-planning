import json
from z3 import *

def main():
    # Define the sorts and constants for each attribute
    NameSort, (Bob, Arnold, Alice, Peter, Eric) = EnumSort('Name', ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric'])
    HobbySort, (cooking, gardening, painting, photography, knitting) = EnumSort('Hobby', ['cooking', 'gardening', 'painting', 'photography', 'knitting'])
    SportSort, (swimming, tennis, soccer, baseball, basketball) = EnumSort('Sport', ['swimming', 'tennis', 'soccer', 'baseball', 'basketball'])
    StyleSort, (ranch, craftsman, victorian, modern, colonial) = EnumSort('Style', ['ranch', 'craftsman', 'victorian', 'modern', 'colonial'])
    ChildSort, (Timothy, Samantha, Bella, Meredith, Fred) = EnumSort('Child', ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred'])
    HeightSort, (average, very_tall, very_short, short, tall) = EnumSort('Height', ['average', 'very_tall', 'very_short', 'short', 'tall'])
    
    # Create variables for each house (0-indexed: house0 = house1, house1 = house2, etc.)
    names = [Const(f'name_{i}', NameSort) for i in range(5)]
    hobbies = [Const(f'hobby_{i}', HobbySort) for i in range(5)]
    sports = [Const(f'sport_{i}', SportSort) for i in range(5)]
    styles = [Const(f'style_{i}', StyleSort) for i in range(5)]
    children = [Const(f'child_{i}', ChildSort) for i in range(5)]
    heights = [Const(f'height_{i}', HeightSort) for i in range(5)]
    
    s = Solver()
    
    # Each attribute must have distinct values across houses
    s.add(Distinct(names))
    s.add(Distinct(hobbies))
    s.add(Distinct(sports))
    s.add(Distinct(styles))
    s.add(Distinct(children))
    s.add(Distinct(heights))
    
    # Add constraints from clues
    # Clue 1: The person who has an average height is the person's child is named Meredith.
    s.add(Or([And(heights[i] == average, children[i] == Meredith) for i in range(5)]))
    
    # Clue 2: The person who is tall is in the second house.
    s.add(heights[1] == tall)
    
    # Clue 3: Peter is directly left of the person residing in a Victorian house.
    s.add(Or([And(names[i] == Peter, styles[i+1] == victorian) for i in range(4)]))
    
    # Clue 4: Alice is the person who is tall.
    s.add(Or([And(names[i] == Alice, heights[i] == tall) for i in range(5)]))
    
    # Clue 5: The person who loves baseball is the person who is very tall.
    s.add(Or([And(sports[i] == baseball, heights[i] == very_tall) for i in range(5)]))
    
    # Clue 6: The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
    s.add(Or([And(children[i] == Meredith, children[i+1] == Timothy) for i in range(4)] +
             [And(children[i] == Timothy, children[i+1] == Meredith) for i in range(4)]))
    
    # Clue 7: Bob is the person who paints as a hobby.
    s.add(Or([And(names[i] == Bob, hobbies[i] == painting) for i in range(5)]))
    
    # Clue 8: The person who enjoys gardening is in the second house.
    s.add(hobbies[1] == gardening)
    
    # Clue 9: The person who is very short is somewhere to the right of Eric.
    s.add(Or([And(names[i] == Eric, heights[j] == very_short, j > i) for i in range(5) for j in range(5)]))
    
    # Clue 10: The person who loves tennis is the person's child is named Samantha.
    s.add(Or([And(sports[i] == tennis, children[i] == Samantha) for i in range(5)]))
    
    # Clue 11: The person who loves soccer is not in the first house.
    s.add(sports[0] != soccer)
    
    # Clue 12: The person's child is named Samantha is the person in a modern-style house.
    s.add(Or([And(children[i] == Samantha, styles[i] == modern) for i in range(5)]))
    
    # Clue 13: The person in a Craftsman-style house is the person who has an average height.
    s.add(Or([And(styles[i] == craftsman, heights[i] == average) for i in range(5)]))
    
    # Clue 14: The person's child is named Fred is the person residing in a Victorian house.
    s.add(Or([And(children[i] == Fred, styles[i] == victorian) for i in range(5)]))
    
    # Clue 15: The person who is short is the person who loves basketball.
    s.add(Or([And(heights[i] == short, sports[i] == basketball) for i in range(5)]))
    
    # Clue 16: Peter is the person who is very tall.
    s.add(Or([And(names[i] == Peter, heights[i] == very_tall) for i in range(5)]))
    
    # Clue 17: The person in a ranch-style home is somewhere to the left of the person who loves cooking.
    s.add(Or([And(styles[i] == ranch, hobbies[j] == cooking, i < j) for i in range(5) for j in range(5)]))
    
    # Clue 18: The person who enjoys knitting and the person who enjoys gardening are next to each other.
    s.add(Or([And(hobbies[i] == knitting, hobbies[i+1] == gardening) for i in range(4)] +
             [And(hobbies[i] == gardening, hobbies[i+1] == knitting) for i in range(4)]))
    
    # Clue 19: The person in a modern-style house is the person who loves cooking.
    s.add(Or([And(styles[i] == modern, hobbies[i] == cooking) for i in range(5)]))
    
    # Clue 20: The person residing in a Victorian house is in the fifth house.
    s.add(styles[4] == victorian)
    
    # Check satisfiability and get the model
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(5):
            house_num = str(i+1)
            name_val = m.eval(names[i])
            hobby_val = m.eval(hobbies[i])
            sport_val = m.eval(sports[i])
            style_val = m.eval(styles[i])
            child_val = m.eval(children[i])
            height_val = m.eval(heights[i])
            
            name_str = name_val.decl().name()
            hobby_str = hobby_val.decl().name()
            sport_str = sport_val.decl().name()
            style_str = style_val.decl().name()
            child_str = child_val.decl().name()
            height_str = height_val.decl().name()
            
            rows.append([house_num, name_str, hobby_str, sport_str, style_str, child_str, height_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()