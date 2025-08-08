import json
from z3 import *

def main():
    city_names = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    duration = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }
    fixed_start = {
        "Lisbon": 4,
        "Stockholm": 13,
        "Lyon": 18
    }
    graph = {
        "Dubrovnik": ["Stockholm", "Copenhagen"],
        "Lisbon": ["Copenhagen", "Lyon", "Stockholm", "Prague"],
        "Copenhagen": ["Lisbon", "Stockholm", "Split", "Dubrovnik", "Prague", "Tallinn"],
        "Prague": ["Stockholm", "Lyon", "Lisbon", "Split", "Copenhagen", "Tallinn"],
        "Tallinn": ["Stockholm", "Copenhagen", "Prague"],
        "Stockholm": ["Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Lisbon", "Split"],
        "Split": ["Copenhagen", "Prague", "Lyon", "Stockholm"],
        "Lyon": ["Lisbon", "Prague", "Split"]
    }
    
    s = {city: Int(f's_{city}') for city in city_names}
    order = [Int(f'order_{i}') for i in range(8)]
    
    solver = Solver()
    
    for i in range(8):
        solver.add(order[i] >= 0, order[i] < 8)
    solver.add(Distinct(order))
    
    for city, start in fixed_start.items():
        solver.add(s[city] == start)
    
    for city in city_names:
        solver.add(s[city] >= 1)
        solver.add(s[city] + duration[city] - 1 <= 19)
    
    solver.add(s[city_names[order[0]]] == 1)
    for i in range(7):
        solver.add(s[city_names[order[i+1]]] == s[city_names[order[i]]] + duration[city_names[order[i]]] - 1)
    solver.add(s[city_names[order[7]]] + duration[city_names[order[7]]] - 1 == 19)
    
    for i in range(7):
        city_i = city_names[order[i]]
        city_j = city_names[order[i+1]]
        solver.add(Or([city_j == name for name in graph[city_i]]))
    
    tallinn_constraint = Or(
        And(s["Tallinn"] <= 1, 1 <= s["Tallinn"] + duration["Tallinn"] - 1),
        And(s["Tallinn"] <= 2, 2 <= s["Tallinn"] + duration["Tallinn"] - 1)
    )
    solver.add(tallinn_constraint)
    
    if solver.check() == sat:
        model = solver.model()
        start_days = {city: model.eval(s[city]).as_long() for city in city_names}
        seq_indices = [model.eval(order[i]).as_long() for i in range(8)]
        sequence = [city_names[idx] for idx in seq_indices]
        
        itinerary = []
        for city in sequence:
            start = start_days[city]
            end = start + duration[city] - 1
            for day in range(start, end + 1):
                itinerary.append({"day": day, "place": city})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()