from z3 import *
import json

def main():
    # Create lists for attributes for 6 houses (0-indexed: index0=house1, index1=house2, ...)
    names = [Int('name_%d' % i) for i in range(6)]
    pets = [Int('pet_%d' % i) for i in range(6)]
    styles = [Int('style_%d' % i) for i in range(6)]
    birthdays = [Int('birthday_%d' % i) for i in range(6)]
    
    s = Solver()
    
    # Define the mapping for output
    name_map = {0: 'Peter', 1: 'Bob', 2: 'Carol', 3: 'Eric', 4: 'Alice', 5: 'Arnold'}
    pet_map = {0: 'bird', 1: 'dog', 2: 'cat', 3: 'rabbit', 4: 'fish', 5: 'hamster'}
    style_map = {0: 'victorian', 1: 'ranch', 2: 'modern', 3: 'mediterranean', 4: 'colonial', 5: 'craftsman'}
    birthday_map = {0: 'mar', 1: 'sept', 2: 'may', 3: 'feb', 4: 'jan', 5: 'april'}
    
    # Each attribute is between 0 and 5
    for i in range(6):
        s.add(And(names[i] >= 0, names[i] < 6))
        s.add(And(pets[i] >= 0, pets[i] < 6))
        s.add(And(styles[i] >= 0, styles[i] < 6))
        s.add(And(birthdays[i] >= 0, birthdays[i] < 6))
    
    # All attributes are distinct
    s.add(Distinct(names))
    s.add(Distinct(pets))
    s.add(Distinct(styles))
    s.add(Distinct(birthdays))
    
    # Clue 3: Birthday in May is in the second house (index1)
    s.add(birthdays[1] == 2)  # may is 2
    
    # Clue 4: Colonial style in the second house (index1)
    s.add(styles[1] == 4)     # colonial is 4
    
    # Clue 5: Carol in the third house (index2)
    s.add(names[2] == 2)      # Carol is 2
    
    # Clue 6: Mediterranean style not in the sixth house (index5)
    s.add(styles[5] != 3)     # mediterranean is 3
    
    # Clue 8: Eric in the sixth house (index5)
    s.add(names[5] == 3)      # Eric is 3
    
    # Clue 13: Fish not in second house (index1)
    s.add(pets[1] != 4)       # fish is 4
    
    # Clue 14: Peter is colonial style -> so for the house with colonial style, name is Peter (0)
    for i in range(6):
        s.add(Implies(styles[i] == 4, names[i] == 0))
    
    # Clue 17: Carol (in house3, index2) has birthday in March (0)
    s.add(birthdays[2] == 0)  # march is 0
    
    # Clue 18: Craftsman style in fourth house (index3)
    s.add(styles[3] == 5)     # craftsman is 5
    
    # Clue 19: Dog in fourth house (index3)
    s.add(pets[3] == 1)       # dog is 1
    
    # Clue 11: Craftsman style is Arnold (5) -> so for the house with craftsman style, name is Arnold
    for i in range(6):
        s.add(Implies(styles[i] == 5, names[i] == 5))
    
    # Clue 1: Hamster (5) is to the right of March birthday (0)
    march_index = Int('march_index')
    s.add(Or([And(birthdays[i] == 0, march_index == i) for i in range(6)]))
    hamster_index = Int('hamster_index')
    s.add(Or([And(pets[i] == 5, hamster_index == i) for i in range(6)]))
    s.add(hamster_index > march_index)
    
    # Clue 2: January (4) left of September (1)
    jan_index = Int('jan_index')
    s.add(Or([And(birthdays[i] == 4, jan_index == i) for i in range(6)]))
    sept_index = Int('sept_index')
    s.add(Or([And(birthdays[i] == 1, sept_index == i) for i in range(6)]))
    s.add(jan_index < sept_index)
    
    # Clue 7: Fish (4) is to the right of Bob (1)
    bob_index = Int('bob_index')
    s.add(Or([And(names[i] == 1, bob_index == i) for i in range(6)]))
    fish_index = Int('fish_index')
    s.add(Or([And(pets[i] == 4, fish_index == i) for i in range(6)]))
    s.add(fish_index > bob_index)
    
    # Clue 9: One house between cat (2) and victorian (0)
    s.add(Or(
        Or([And(pets[i] == 2, styles[i+2] == 0) for i in range(4)]),
        Or([And(styles[i] == 0, pets[i+2] == 2) for i in range(4)])
    ))
    
    # Clue 10: Two houses between victorian (0) and hamster (5)
    s.add(Or(
        Or([And(styles[i] == 0, pets[i+3] == 5) for i in range(3)]),
        Or([And(pets[i] == 5, styles[i+3] == 0) for i in range(3)])
    ))
    
    # Clue 12: Colonial (4) left of modern (2)
    colonial_index = Int('colonial_index')
    s.add(Or([And(styles[i] == 4, colonial_index == i) for i in range(6)]))
    modern_index = Int('modern_index')
    s.add(Or([And(styles[i] == 2, modern_index == i) for i in range(6)]))
    s.add(colonial_index < modern_index)
    
    # Clue 15: January (4) directly left of April (5)
    s.add(Or(
        And(birthdays[0] == 4, birthdays[1] == 5),
        And(birthdays[1] == 4, birthdays[2] == 5),
        And(birthdays[2] == 4, birthdays[3] == 5),
        And(birthdays[3] == 4, birthdays[4] == 5),
        And(birthdays[4] == 4, birthdays[5] == 5)
    ))
    
    # Clue 16: One house between bird (0) and modern (2)
    s.add(Or(
        Or([And(pets[i] == 0, styles[i+2] == 2) for i in range(4)]),
        Or([And(styles[i] == 2, pets[i+2] == 0) for i in range(4)])
    ))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract values
        name_vals = [m.evaluate(names[i]).as_long() for i in range(6)]
        pet_vals = [m.evaluate(pets[i]).as_long() for i in range(6)]
        style_vals = [m.evaluate(styles[i]).as_long() for i in range(6)]
        birthday_vals = [m.evaluate(birthdays[i]).as_long() for i in range(6)]
        
        # Map to strings
        sol_rows = []
        for i in range(6):
            house_num = str(i+1)
            name_str = name_map[name_vals[i]]
            pet_str = pet_map[pet_vals[i]]
            style_str = style_map[style_vals[i]]
            birthday_str = birthday_map[birthday_vals[i]]
            sol_rows.append([house_num, name_str, pet_str, style_str, birthday_str])
        
        # Build the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                "rows": sol_rows
            }
        }
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()