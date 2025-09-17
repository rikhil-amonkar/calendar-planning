from z3 import *
import json

def main():
    # Define cities and their indices
    cities = ["Brussels", "London", "Lisbon", "Madrid", "Reykjavik", "Santorini", "Venice"]
    n_cities = len(cities)
    
    # Define direct flight connections (symmetric)
    connections = [
        (0, 6), (6, 0),  # Brussels-Venice
        (0, 1), (1, 0),  # Brussels-London
        (0, 2), (2, 0),  # Brussels-Lisbon
        (0, 4), (4, 0),  # Brussels-Reykjavik
        (0, 3), (3, 0),  # Brussels-Madrid
        (1, 3), (3, 1),  # Madrid-London
        (1, 5), (5, 1),  # Santorini-London
        (1, 4), (4, 1),  # London-Reykjavik
        (1, 2), (2, 1),  # Lisbon-London
        (2, 4), (4, 2),  # Lisbon-Reykjavik
        (2, 3), (3, 2),  # Lisbon-Madrid
        (2, 6), (6, 2),  # Lisbon-Venice
        (3, 4), (4, 3),  # Reykjavik-Madrid
        (3, 5), (5, 3),  # Madrid-Santorini
        (3, 6), (6, 3),  # Venice-Madrid
        (5, 6), (6, 5),  # Venice-Santorini
        (1, 6), (6, 1)   # Venice-London
    ]
    
    n_days = 17
    s = Solver()
    
    # base_city[i] for day i (1-indexed days 1..17)
    base_city = [Int('base_city_%d' % i) for i in range(1, n_days+1)]
    fly = [Bool('fly_%d' % i) for i in range(1, n_days+1)]
    dest_city = [Int('dest_city_%d' % i) for i in range(1, n_days+1)]
    
    # Domain constraints for base_city and dest_city
    for i in range(n_days):
        s.add(And(base_city[i] >= 0, base_city[i] < n_cities))
        s.add(Implies(fly[i], And(dest_city[i] >= 0, dest_city[i] < n_cities)))
    
    # Continuity constraint: base_city of next day equals destination if flying, else same city
    for i in range(n_days-1):
        s.add(base_city[i+1] == If(fly[i], dest_city[i], base_city[i]))
    
    # Flight constraints: if flying, must be connected and not same city
    for i in range(n_days):
        s.add(Implies(fly[i], Or([And(base_city[i] == c1, dest_city[i] == c2) for (c1, c2) in connections])))
        s.add(Implies(fly[i], base_city[i] != dest_city[i]))
    
    # Brussels conference on day 1 and 2
    s.add(Or(base_city[0] == 0, And(fly[0], dest_city[0] == 0)))  # Day 1
    s.add(Or(base_city[1] == 0, And(fly[1], dest_city[1] == 0)))  # Day 2
    
    # Madrid wedding between day 7-11 (0-indexed: 6 to 10)
    madrid_days = []
    for i in range(6, 11):
        madrid_days.append(Or(base_city[i] == 3, And(fly[i], dest_city[i] == 3)))
    s.add(Or(madrid_days))
    
    # Venice relatives between day 5-7 (0-indexed: 4 to 6)
    venice_days = []
    for i in range(4, 7):
        venice_days.append(Or(base_city[i] == 6, And(fly[i], dest_city[i] == 6)))
    s.add(Or(venice_days))
    
    # Total days per city
    req_days = [2, 3, 4, 5, 3, 3, 3]  # Brussels, London, Lisbon, Madrid, Reykjavik, Santorini, Venice
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            presence = Or(base_city[i] == c, And(fly[i], dest_city[i] == c))
            total += If(presence, 1, 0)
        s.add(total == req_days[c])
    
    # Exactly 6 flight days
    total_flights = Sum([If(fly[i], 1, 0) for i in range(n_days)])
    s.add(total_flights == 6)
    
    if s.check() == sat:
        m = s.model()
        presence_dict = {c: [] for c in range(n_cities)}
        
        for i in range(n_days):
            base_val = m.evaluate(base_city[i]).as_long()
            fly_val = is_true(m.evaluate(fly[i]))
            presence_dict[base_val].append(i+1)
            if fly_val:
                dest_val = m.evaluate(dest_city[i]).as_long()
                presence_dict[dest_val].append(i+1)
        
        itinerary = []
        for c in range(n_cities):
            days = sorted(presence_dict[c])
            if not days:
                continue
            start = days[0]
            current = start
            for d in days[1:]:
                if d == current + 1:
                    current = d
                else:
                    if start == current:
                        day_range = f"Day {start}"
                    else:
                        day_range = f"Day {start}-{current}"
                    itinerary.append({"day_range": day_range, "place": cities[c]})
                    start = d
                    current = d
            if start == current:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{current}"
            itinerary.append({"day_range": day_range, "place": cities[c]})
        
        itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()