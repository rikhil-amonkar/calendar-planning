from z3 import *

def main():
    # Define the attribute options
    names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']
    
    n_houses = 5
    # Create Z3 variables for each attribute for each house (0-indexed: house0 = house1, house1 = house2, ...)
    Name = [Int('Name_%d' % i) for i in range(n_houses)]
    Smoothie = [Int('Smoothie_%d' % i) for i in range(n_houses)]
    Nationality = [Int('Nationality_%d' % i) for i in range(n_houses)]
    
    s = Solver()
    
    # Each attribute must be in [0, 4] (indices)
    for i in range(n_houses):
        s.add(Name[i] >= 0, Name[i] <= 4)
        s.add(Smoothie[i] >= 0, Smoothie[i] <= 4)
        s.add(Nationality[i] >= 0, Nationality[i] <= 4)
    
    # All attributes are distinct
    s.add(Distinct(Name))
    s.add(Distinct(Smoothie))
    s.add(Distinct(Nationality))
    
    # Fixed assignments from clues
    # Clue 2: Dragonfruit smoothie in second house (house index1)
    s.add(Smoothie[1] == 4)  # dragonfruit is index4
    # Clue 10 and 11: Alice in third house (index2) and Watermelon smoothie in third house
    s.add(Name[2] == 4)       # Alice is index4
    s.add(Smoothie[2] == 1)   # watermelon is index1
    # Clue 9: Alice is Norwegian
    s.add(Nationality[2] == 2) # norwegian is index2
    # Clue 6: Swedish person in first house (left of dragonfruit in house2)
    s.add(Nationality[0] == 1) # swede is index1
    
    # Clue 1: Dragonfruit (house index1) is left of Eric (Eric is name index1)
    # Eric must be in a house with index > 1 (i.e., house3,4,5 in 0-indexed: indices2,3,4)
    for j in range(n_houses):
        s.add(If(Name[j] == 1, j > 1, True))
    
    # Clue 3: Peter (name index3) not in first house (index0)
    s.add(Name[0] != 3)
    
    # Clue 4: Dane (nationality index3) and British (nationality index4) are adjacent
    adjacent_pairs = []
    for i in range(n_houses-1):
        adjacent_pairs.append((i, i+1))
    or_conditions = []
    for (i, j) in adjacent_pairs:
        or_conditions.append(And(Nationality[i] == 3, Nationality[j] == 4))
        or_conditions.append(And(Nationality[i] == 4, Nationality[j] == 3))
    s.add(Or(or_conditions))
    
    # Clue 5: Desert smoothie (index0) not in fifth house (index4)
    s.add(Smoothie[4] != 0)
    
    # Clue 7: Two houses between Lime smoothie (index2) and the Dane (nationality index3)
    # This means |position(lime) - position(dane)| = 3 (since two houses between implies three apart in 0-indexed indices)
    # Possible pairs: (0,3), (3,0), (1,4), (4,1)
    lime_dane_pairs = [
        And(Smoothie[0] == 2, Nationality[3] == 3),
        And(Smoothie[3] == 2, Nationality[0] == 3),
        And(Smoothie[1] == 2, Nationality[4] == 3),
        And(Smoothie[4] == 2, Nationality[1] == 3)
    ]
    s.add(Or(lime_dane_pairs))
    
    # Clue 8: Bob (name index2) is the Dane (nationality index3)
    for i in range(n_houses):
        s.add(If(Name[i] == 2, Nationality[i] == 3, True))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        solution_rows = []
        for i in range(n_houses):
            name_index = model[Name[i]].as_long()
            smoothie_index = model[Smoothie[i]].as_long()
            nationality_index = model[Nationality[i]].as_long()
            house_num = i + 1
            name_val = names[name_index]
            smoothie_val = smoothies[smoothie_index]
            nationality_val = nationalities[nationality_index]
            solution_rows.append([str(house_num), name_val, smoothie_val, nationality_val])
        
        # Prepare the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": solution_rows
            }
        }
        # Output as JSON string (though the problem requires the code to output the solution, we return the dict)
        # But note: the problem says "Your output should be a JSON-formatted dictionary" - we build the dict and then print it as JSON?
        # However, the problem requires the code to be runnable and output the solution in the specified format.
        # We are to write the Python code that when run, prints the JSON. But the problem says: "Write a Python program that solves it using the Z3 solver."
        # So we'll print the JSON string at the end.
        import json
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()