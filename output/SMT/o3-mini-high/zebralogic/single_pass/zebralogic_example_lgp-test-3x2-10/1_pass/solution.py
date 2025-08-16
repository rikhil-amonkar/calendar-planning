from z3 import *
import json

def main():
    # Define house positions for each person (1,2,3)
    house_Eric = Int('house_Eric')
    house_Arnold = Int('house_Arnold')
    house_Peter = Int('house_Peter')
    
    # Define heights for each person.
    # We use the following mapping for clarity:
    # 1 -> "short"
    # 2 -> "very short"
    # 3 -> "average"
    height_Eric = Int('height_Eric')
    height_Arnold = Int('height_Arnold')
    height_Peter = Int('height_Peter')
    
    s = Solver()
    
    # Houses can be 1, 2, or 3, and they must be different.
    s.add(And(house_Eric >= 1, house_Eric <= 3))
    s.add(And(house_Arnold >= 1, house_Arnold <= 3))
    s.add(And(house_Peter >= 1, house_Peter <= 3))
    s.add(Distinct(house_Eric, house_Arnold, house_Peter))
    
    # Heights must be one of 1, 2, or 3 and all different.
    s.add(And(height_Eric >= 1, height_Eric <= 3))
    s.add(And(height_Arnold >= 1, height_Arnold <= 3))
    s.add(And(height_Peter >= 1, height_Peter <= 3))
    s.add(Distinct(height_Eric, height_Arnold, height_Peter))
    
    # Clue 1: Eric is not in the first house.
    s.add(house_Eric != 1)
    
    # Clue 4: Arnold is not in the first house.
    s.add(house_Arnold != 1)
    
    # Clue 3: The person who is very short is Eric.
    # According to our mapping, "very short" is 2.
    s.add(height_Eric == 2)
    
    # Clue 2: The person who is very short is somewhere to the left 
    # of the person who is short. Since "very short" is 2 and "short" is 1,
    # we enforce: if a person has height 1 ("short") then Eric's house is to its left.
    s.add(Implies(height_Arnold == 1, house_Eric < house_Arnold))
    s.add(Implies(height_Peter == 1, house_Eric < house_Peter))
    
    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        
        # Assemble the solution for each person.
        # Each tuple is (Name, House_position, Height_code)
        people = [
            ("Eric", m[house_Eric].as_long(), m[height_Eric].as_long()),
            ("Arnold", m[house_Arnold].as_long(), m[height_Arnold].as_long()),
            ("Peter", m[house_Peter].as_long(), m[height_Peter].as_long())
        ]
        
        # Mapping from our integer encoding to height description.
        height_map = {
            1: "short",
            2: "very short",
            3: "average"
        }
        
        # Sort people by their house number.
        sorted_people = sorted(people, key=lambda x: x[1])
        
        # Build the rows in the required format: [House, Name, Height]
        rows = []
        for name, house, height_val in sorted_people:
            rows.append([str(house), name, height_map[height_val]])
        
        # Create final JSON structure.
        output = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()