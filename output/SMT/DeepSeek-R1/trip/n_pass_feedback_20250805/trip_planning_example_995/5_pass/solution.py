from z3 import *
import json

def main():
    # City definitions
    city_names = ['Barcelona', 'Oslo', 'Stuttgart', 'Venice', 'Split', 'Brussels', 'Copenhagen']
    city_to_index = {name: idx for idx, name in enumerate(city_names)}
    days_req = [3, 2, 3, 4, 4, 3, 3]
    
    # Flight connections
    edges = [
        ("Venice", "Stuttgart"), ("Oslo", "Brussels"), ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"), ("Barcelona", "Venice"), ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"), ("Copenhagen", "Brussels"), ("Oslo", "Split"),
        ("Oslo", "Venice"), ("Barcelona", "Split"), ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"), ("Copenhagen", "Stuttgart"), ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"), ("Barcelona", "Brussels")
    ]
    
    # Normalize edges
    normalized_edges = set()
    for a, b in edges:
        u, v = city_to_index[a], city_to_index[b]
        normalized_edges.add((min(u, v), max(u, v)))
    
    # Z3 variables
    c = [Int(f'c_{i}') for i in range(7)]  # City sequence
    s = [Int(f's_{i}') for i in range(7)]  # Start days
    e = [Int(f'e_{i}') for i in range(7)]  # End days
    
    solver = Solver()
    
    # First city is Barcelona (index 0)
    solver.add(c[0] == 0)
    solver.add(s[0] == 1)
    
    # All cities distinct and valid
    solver.add(Distinct(c))
    for i in range(7):
        solver.add(And(c[i] >= 0, c[i] < 7))
    
    # Duration lookup function
    def get_duration(city):
        expr = days_req[6]  # Default to last city
        for i in range(5, -1, -1):  # Build conditions from 5 down to 0
            expr = If(city == i, days_req[i], expr)
        return expr
    
    # Stay duration constraints
    for k in range(7):
        duration = get_duration(c[k])
        solver.add(e[k] - s[k] + 1 == duration)  # Explicit duration constraint
    
    # Consecutive city constraints
    for k in range(1, 7):
        solver.add(s[k] == e[k-1])  # Next city starts when previous ends
    
    # Total trip ends on day 16
    solver.add(e[6] == 16)
    
    # Flight connections between consecutive cities
    for k in range(6):
        u, v = c[k], c[k+1]
        edge_constraints = []
        for a, b in normalized_edges:
            edge_constraints.append(Or(And(u == a, v == b), And(u == b, v == a)))
        solver.add(Or(edge_constraints))
    
    # Oslo must include day 3 or 4
    oslo_constraints = []
    for k in range(7):
        oslo_constraints.append(
            And(c[k] == 1, 
                Or(And(s[k] <= 3, e[k] >= 3), 
                   And(s[k] <= 4, e[k] >= 4)))
        )
    solver.add(Or(oslo_constraints))
    
    # Brussels must include day 9, 10, or 11
    brussels_constraints = []
    for k in range(7):
        brussels_constraints.append(
            And(c[k] == 5,
                Or(And(s[k] <= 9, e[k] >= 9),
                   And(s[k] <= 10, e[k] >= 10),
                   And(s[k] <= 11, e[k] >= 11)))
        )
    solver.add(Or(brussels_constraints))
    
    # Solve and output itinerary
    if solver.check() == sat:
        model = solver.model()
        c_val = [model.evaluate(city).as_long() for city in c]
        s_val = [model.evaluate(start).as_long() for start in s]
        e_val = [model.evaluate(end).as_long() for end in e]
        
        itinerary = []
        for day in range(1, 17):  # Days 1-16
            current_cities = []
            for i in range(7):
                if s_val[i] <= day <= e_val[i]:
                    current_cities.append(city_names[c_val[i]])
            itinerary.append({"day": day, "place": ", ".join(current_cities)})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()