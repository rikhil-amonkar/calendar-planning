from z3 import *
import json

def main():
    # Define enums for names and heights
    Name, (Peter, Alice, Bob, Eric, Arnold) = EnumSort('Name', ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold'])
    Height, (very_tall, average, tall, very_short, short) = EnumSort('Height', ['very_tall', 'average', 'tall', 'very_short', 'short'])
    
    # Create variables for names and heights of houses 1 to 5 (index 0 to 4)
    n_vars = [Const('n%d' % i, Name) for i in range(1, 6)]
    h_vars = [Const('h%d' % i, Height) for i in range(1, 6)]
    
    s = Solver()
    
    # All names and heights are distinct
    s.add(Distinct(n_vars))
    s.add(Distinct(h_vars))
    
    # Clue 1: The person who is short is in the second house (index 1)
    s.add(h_vars[1] == short)
    
    # Clue 2: Peter is directly left of Bob
    s.add(Or(
        And(n_vars[0] == Peter, n_vars[1] == Bob),
        And(n_vars[1] == Peter, n_vars[2] == Bob),
        And(n_vars[2] == Peter, n_vars[3] == Bob),
        And(n_vars[3] == Peter, n_vars[4] == Bob)
    ))
    
    # Clue 3: Eric is somewhere to the left of Peter
    s.add(Or(
        And(n_vars[0] == Eric, Or(n_vars[1] == Peter, n_vars[2] == Peter, n_vars[3] == Peter, n_vars[4] == Peter)),
        And(n_vars[1] == Eric, Or(n_vars[2] == Peter, n_vars[3] == Peter, n_vars[4] == Peter)),
        And(n_vars[2] == Eric, Or(n_vars[3] == Peter, n_vars[4] == Peter)),
        And(n_vars[3] == Eric, n_vars[4] == Peter)
    ))
    
    # Clue 4: The person who is very tall is directly left of Peter
    s.add(Or(
        And(h_vars[0] == very_tall, n_vars[1] == Peter),
        And(h_vars[1] == very_tall, n_vars[2] == Peter),
        And(h_vars[2] == very_tall, n_vars[3] == Peter),
        And(h_vars[3] == very_tall, n_vars[4] == Peter)
    ))
    
    # Clue 5: Alice is directly left of the person who has average height
    # Clue 7: The person with average height is in the fifth house (index 4)
    s.add(n_vars[3] == Alice)
    s.add(h_vars[4] == average)
    
    # Clue 6: The person who is short (house2, index1) and very short are next to each other
    s.add(Or(h_vars[0] == very_short, h_vars[2] == very_short))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(5):
            house_num = str(i + 1)
            name_val = m.eval(n_vars[i])
            height_val = m.eval(h_vars[i])
            name_str = str(name_val)
            height_str = str(height_val)
            # Adjust height strings for output
            if height_str == 'very_tall':
                height_str = 'very tall'
            elif height_str == 'very_short':
                height_str = 'very short'
            rows.append([house_num, name_str, height_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()