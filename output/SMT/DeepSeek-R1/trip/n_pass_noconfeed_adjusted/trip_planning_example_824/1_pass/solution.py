import json
from z3 import *

def main():
    # Define cities and their indices
    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    n = len(cities)
    c_index = {c: i for i, c in enumerate(cities)}
    
    # Define direct flight connections (undirected)
    connections = [
        (c_index['Lisbon'], c_index['Bucharest']),
        (c_index['Berlin'], c_index['Lisbon']),
        (c_index['Bucharest'], c_index['Riga']),
        (c_index['Berlin'], c_index['Riga']),
        (c_index['Split'], c_index['Lyon']),
        (c_index['Lisbon'], c_index['Riga']),
        (c_index['Riga'], c_index['Tallinn']),
        (c_index['Berlin'], c_index['Split']),
        (c_index['Lyon'], c_index['Lisbon']),
        (c_index['Berlin'], c_index['Tallinn']),
        (c_index['Lyon'], c_index['Bucharest'])
    ]
    
    # Create connection matrix
    connected = [[False] * n for _ in range(n)]
    for i, j in connections:
        connected[i][j] = True
        connected[j][i] = True
    
    # Initialize solver
    s = Solver()
    
    # Define variables for start and end days of each city
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    
    # Fixed constraints for Berlin
    berlin = c_index['Berlin']
    s.add(start[berlin] == 1)
    s.add(end[berlin] == 5)
    
    # Fixed constraints for Lyon
    lyon = c_index['Lyon']
    s.add(start[lyon] == 7)
    s.add(end[lyon] == 11)
    
    # Fixed constraints for Bucharest
    bucharest = c_index['Bucharest']
    s.add(start[bucharest] == 13)
    s.add(end[bucharest] == 15)
    
    # Duration constraints for other cities
    split = c_index['Split']
    s.add(end[split] - start[split] + 1 == 3)
    
    riga = c_index['Riga']
    s.add(end[riga] - start[riga] + 1 == 5)
    
    lisbon = c_index['Lisbon']
    s.add(end[lisbon] - start[lisbon] + 1 == 3)
    
    tallinn = c_index['Tallinn']
    s.add(end[tallinn] - start[tallinn] + 1 == 4)
    
    # General constraints: valid day ranges
    for i in range(n):
        s.add(start[i] >= 1)
        s.add(end[i] <= 22)
        s.add(start[i] <= end[i])
    
    # Coverage constraint: every day must be covered by at least one city
    for d in range(1, 23):
        cover_constraints = []
        for i in range(n):
            cover_constraints.append(And(start[i] <= d, d <= end[i]))
        s.add(Or(cover_constraints))
    
    # Disjointness constraint: city stays can only overlap at boundaries
    for i in range(n):
        for j in range(i + 1, n):
            s.add(Or(
                end[i] < start[j],
                end[j] < start[i],
                end[i] == start[j],
                end[j] == start[i]
            ))
    
    # Flight connection constraint for adjacent cities
    for i in range(n):
        for j in range(n):
            if i != j:
                s.add(Implies(Or(end[i] == start[j], end[j] == start[i]), connected[i][j]))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(n):
            s_val = m.evaluate(start[i]).as_long()
            e_val = m.evaluate(end[i]).as_long()
            itinerary_list.append((s_val, e_val, cities[i]))
        itinerary_list.sort(key=lambda x: x[0])
        result = {"itinerary": []}
        for s_val, e_val, city in itinerary_list:
            result["itinerary"].append({"day_range": f"Day {s_val}-{e_val}", "place": city})
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()