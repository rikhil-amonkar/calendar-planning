from z3 import *
import json

def main():
    # City names and mapping to indices
    city_names = ['Barcelona', 'Oslo', 'Stuttgart', 'Venice', 'Split', 'Brussels', 'Copenhagen']
    city_to_index = {name: idx for idx, name in enumerate(city_names)}
    
    # Required days per city: [Barcelona, Oslo, Stuttgart, Venice, Split, Brussels, Copenhagen]
    days_req = [3, 2, 3, 4, 4, 3, 3]
    
    # Define direct flight connections (as tuples of city indices)
    edges_by_name = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels")
    ]
    
    # Build normalized_edges set (each edge as (min, max))
    normalized_edges = set()
    for (a, b) in edges_by_name:
        u = city_to_index[a]
        v = city_to_index[b]
        normalized_edges.add((min(u, v), max(u, v)))
    
    # Create Z3 variables
    c = [Int('c_%d' % i) for i in range(7)]  # city at each position
    s = [Int('s_%d' % i) for i in range(7)]  # start day for each position
    e = [Int('e_%d' % i) for i in range(7)]  # end day for each position
    
    solver = Solver()
    
    # Constraint: First city is Barcelona (index 0)
    solver.add(c[0] == 0)
    solver.add(s[0] == 1)
    solver.add(e[0] == s[0] + days_req[0] - 1)  # Barcelona: 1 + (3-1) = 3
    
    # Constraint: All cities are distinct and within valid range
    solver.add(Distinct(c))
    for i in range(7):
        solver.add(And(c[i] >= 0, c[i] < 7))
    
    # Function to get required days for a city index
    def get_req(city):
        return If(city == 0, days_req[0],
            If(city == 1, days_req[1],
            If(city == 2, days_req[2],
            If(city == 3, days_req[3],
            If(city == 4, days_req[4],
            If(city == 5, days_req[5], days_req[6])))))
    
    # Constraints for positions 1 to 6
    for k in range(1, 7):
        solver.add(s[k] == e[k-1])  # Start day is end day of previous city
        solver.add(e[k] == s[k] + get_req(c[k]) - 1)
    
    # Last city ends on day 16
    solver.add(e[6] == 16)
    
    # Flight constraints for consecutive cities
    for k in range(6):  # 0 to 5
        u = c[k]
        v = c[k+1]
        # Create disjunction for all possible edges
        edge_conds = []
        for edge in normalized_edges:
            a, b = edge
            cond = Or(And(u == a, v == b), And(u == b, v == a))
            edge_conds.append(cond)
        solver.add(Or(edge_conds))
    
    # Constraint for Oslo (city index 1): must include day 3 or 4
    oslo_cond = []
    for k in range(7):
        cond = And(c[k] == 1, 
                   Or(And(s[k] <= 3, e[k] >= 3), 
                      And(s[k] <= 4, e[k] >= 4)))
        oslo_cond.append(cond)
    solver.add(Or(oslo_cond))
    
    # Constraint for Brussels (city index 5): must include day 9, 10, or 11
    brussels_cond = []
    for k in range(7):
        cond = And(c[k] == 5,
                   Or(And(s[k] <= 9, e[k] >= 9),
                      And(s[k] <= 10, e[k] >= 10),
                      And(s[k] <= 11, e[k] >= 11)))
        brussels_cond.append(cond)
    solver.add(Or(brussels_cond))
    
    # Solve the constraints
    if solver.check() == sat:
        m = solver.model()
        # Extract values for c, s, e
        c_val = [m.evaluate(c[i]).as_long() for i in range(7)]
        s_val = [m.evaluate(s[i]).as_long() for i in range(7)]
        e_val = [m.evaluate(e[i]).as_long() for i in range(7)]
        
        # Build itinerary
        itinerary_list = []
        for day in range(1, 17):  # Days 1 to 16
            places = []
            for pos in range(7):
                if s_val[pos] <= day <= e_val[pos]:
                    city_idx = c_val[pos]
                    places.append(city_names[city_idx])
            # Sort places by their start day to maintain sequence order
            itinerary_list.append({"day": day, "place": ", ".join(places)})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()