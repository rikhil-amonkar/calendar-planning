from z3 import *
import json

def main():
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    connections_list = [
        "Reykjavik and Munich", "Munich and Frankfurt", "Split and Oslo", "Reykjavik and Oslo", 
        "Bucharest and Munich", "Oslo and Frankfurt", "Bucharest and Barcelona", "Barcelona and Frankfurt", 
        "Reykjavik and Frankfurt", "Barcelona and Stockholm", "Barcelona and Reykjavik", "Stockholm and Reykjavik", 
        "Barcelona and Split", "Bucharest and Oslo", "Bucharest and Frankfurt", "Split and Stockholm", 
        "Barcelona and Oslo", "Stockholm and Munich", "Stockholm and Oslo", "Split and Frankfurt", 
        "Barcelona and Munich", "Stockholm and Frankfurt", "Munich and Oslo", "Split and Munich"
    ]
    
    connected_pairs_index = set()
    for conn in connections_list:
        a, b = conn.split(' and ')
        a = a.strip()
        b = b.strip()
        i = city_index[a]
        j = city_index[b]
        if i < j:
            pair = (i, j)
        else:
            pair = (j, i)
        connected_pairs_index.add(pair)
    
    all_pairs = set()
    for i in range(8):
        for j in range(i+1, 8):
            all_pairs.add((i, j))
    
    non_connected_pairs = all_pairs - connected_pairs_index

    X = [[Bool(f'x_day_{d}_city_{c}') for c in range(8)] for d in range(20)]
    s = Solver()
    
    # Constraint 1: Each day has either 1 or 2 cities
    for d in range(20):
        total_cities = Sum([If(X[d][c], 1, 0) for c in range(8)])
        s.add(Or(total_cities == 1, total_cities == 2))
    
    # Constraint 2: Non-connected pairs cannot be together on the same day
    for d in range(20):
        for (i, j) in non_connected_pairs:
            s.add(Not(And(X[d][i], X[d][j])))
    
    # Constraint 3: Consecutive days must share at least one city
    for d in range(19):
        s.add(Or([And(X[d][c], X[d+1][c]) for c in range(8)]))
    
    # Constraint 4: Total days per city
    s.add(Sum([If(X[d][city_index['Oslo']], 1, 0) for d in range(20)]) == 2)
    s.add(Sum([If(X[d][city_index['Reykjavik']], 1, 0) for d in range(20)]) == 5)
    s.add(Sum([If(X[d][city_index['Stockholm']], 1, 0) for d in range(20)]) == 4)
    s.add(Sum([If(X[d][city_index['Munich']], 1, 0) for d in range(20)]) == 4)
    s.add(Sum([If(X[d][city_index['Frankfurt']], 1, 0) for d in range(20)]) == 4)
    s.add(Sum([If(X[d][city_index['Barcelona']], 1, 0) for d in range(20)]) == 3)
    s.add(Sum([If(X[d][city_index['Bucharest']], 1, 0) for d in range(20)]) == 2)
    s.add(Sum([If(X[d][city_index['Split']], 1, 0) for d in range(20)]) == 3)
    
    # Constraint 5: Specific events
    # Oslo: must be present on day 16 and 17 (index 15 and 16)
    s.add(X[15][city_index['Oslo']])
    s.add(X[16][city_index['Oslo']])
    # Reykjavik: must be present between day 9 and 13 (index 8 to 12)
    s.add(Or([X[d][city_index['Reykjavik']] for d in range(8, 13)]))
    # Munich: must be present between day 13 and 16 (index 12 to 15)
    s.add(Or([X[d][city_index['Munich']] for d in range(12, 16)]))
    # Frankfurt: must be present between day 17 and 20 (index 16 to 19)
    s.add(Or([X[d][city_index['Frankfurt']] for d in range(16, 20)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(20):
            for c_idx, city in enumerate(cities):
                if is_true(m.evaluate(X[d][c_idx])):
                    itinerary.append({"day": d+1, "place": city})
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()