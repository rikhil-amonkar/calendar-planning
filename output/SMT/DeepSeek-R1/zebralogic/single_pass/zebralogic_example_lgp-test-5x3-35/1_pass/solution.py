from z3 import *

def main():
    # Define enums for attributes
    NameSort, (Eric, Peter, Arnold, Alice, Bob) = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob'])
    MotherSort, (Kailyn, Janelle, Aniya, Penny, Holly) = EnumSort('Mother', ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly'])
    HeightSort, (average, very_short, short, very_tall, tall) = EnumSort('Height', ['average', 'very short', 'short', 'very tall', 'tall'])
    
    # Create variables for each house (0 to 4 for houses 1 to 5)
    n = [Const(f'n_{i}', NameSort) for i in range(5)]
    m = [Const(f'm_{i}', MotherSort) for i in range(5)]
    h = [Const(f'h_{i}', HeightSort) for i in range(5)]
    
    s = Solver()
    
    # All names, mothers, heights are distinct
    s.add(Distinct(n))
    s.add(Distinct(m))
    s.add(Distinct(h))
    
    # Clue 1: Alice is the person whose mother's name is Aniya.
    s.add(Or([And(n[i] == Alice, m[i] == Aniya) for i in range(5)]))
    
    # Clue 2: The person with average height is left of the person with mother Penny.
    avg_idx = [h[i] == average for i in range(5)]
    penny_m_idx = [m[i] == Penny for i in range(5)]
    s.add(Or([And(avg_idx[i], penny_m_idx[j]) for i in range(5) for j in range(5) if i < j]))
    
    # Clue 3: The person whose mother's name is Janelle is Bob.
    s.add(Or([And(m[i] == Janelle, n[i] == Bob) for i in range(5)]))
    
    # Clue 4: Peter is not in the second house (index 1).
    s.add(n[1] != Peter)
    
    # Clue 5: The person who is short is directly left of Arnold.
    s.add(Or([And(h[i] == short, n[i+1] == Arnold) for i in range(4)]))
    
    # Clue 6: The person who is very tall is Arnold.
    s.add(Or([And(h[i] == very_tall, n[i] == Arnold) for i in range(5)]))
    
    # Clue 7: Bob is directly left of the person with average height.
    s.add(Or([And(n[i] == Bob, h[i+1] == average) for i in range(4)]))
    
    # Clue 8: Eric is not in the fifth house (index 4).
    s.add(n[4] != Eric)
    
    # Clue 9: The person who is very tall is to the right of the person with mother Holly.
    very_tall_idx = [h[i] == very_tall for i in range(5)]
    holly_m_idx = [m[i] == Holly for i in range(5)]
    s.add(Or([And(holly_m_idx[i], very_tall_idx[j]) for i in range(5) for j in range(5) if i < j]))
    
    # Clue 10: Eric is the person whose mother's name is Kailyn.
    s.add(Or([And(n[i] == Eric, m[i] == Kailyn) for i in range(5)]))
    
    # Clue 11: The person who is very short is in the fifth house (index 4).
    s.add(h[4] == very_short)
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        solution = []
        for i in range(5):
            name_val = model.eval(n[i])
            mother_val = model.eval(m[i])
            height_val = model.eval(h[i])
            solution.append((
                str(i+1),
                str(name_val),
                str(mother_val),
                str(height_val)
            ))
        
        # Format as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": solution
            }
        }
        import json
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()