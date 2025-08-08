from z3 import *

def main():
    city_to_index = {
        "Riga": 0,
        "Frankfurt": 1,
        "Amsterdam": 2,
        "Vilnius": 3,
        "London": 4,
        "Stockholm": 5,
        "Bucharest": 6
    }
    index_to_city = {v: k for k, v in city_to_index.items()}
    req_array = [2, 3, 2, 5, 2, 3, 4]  # Days required for each city

    edges_list = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    ]
    directed_edges = []
    for u, v in edges_list:
        a, b = city_to_index[u], city_to_index[v]
        directed_edges.append((a, b))
        directed_edges.append((b, a))

    s = Solver()

    # City sequence variables
    P = [Int('P%d' % i) for i in range(7)]
    for i in range(7):
        s.add(And(P[i] >= 0, P[i] <= 6))
    s.add(Distinct(P))

    # Start day variables for each city
    S = [Int('S%d' % i) for i in range(7)]
    s.add(S[0] == 1)  # First city starts on day 1

    # Create Z3 array for requirements
    Req = Array('Req', IntSort(), IntSort())
    for i in range(7):
        s.add(Req[i] == req_array[i])

    # Constraints for start days
    for i in range(1, 7):
        s.add(S[i] == S[i-1] + Req[P[i-1]] - 1)
    
    # Last city must end on day 15
    s.add(S[6] + Req[P[6]] - 1 == 15)

    # Event constraints
    # Amsterdam must start on day 2
    ams_constraint = Or([And(P[i] == 2, S[i] == 2) for i in range(7)])
    # Vilnius must start on day 7
    vil_constraint = Or([And(P[i] == 3, S[i] == 7) for i in range(7)])
    # Stockholm must start on or after day 12
    stock_constraint = Or([And(P[i] == 5, S[i] >= 12) for i in range(7)])
    
    s.add(ams_constraint)
    s.add(vil_constraint)
    s.add(stock_constraint)

    # Direct flight constraints
    for i in range(6):
        constraints = []
        for a, b in directed_edges:
            constraints.append(And(P[i] == a, P[i+1] == b))
        s.add(Or(constraints))

    if s.check() == sat:
        model = s.model()
        P_val = [model.evaluate(P[i]).as_long() for i in range(7)]
        S_val = [model.evaluate(S[i]).as_long() for i in range(7)]
        Req_val = [req_array[i] for i in range(7)]
        
        city_sequence = [index_to_city[idx] for idx in P_val]
        durations = [Req_val[P_val[i]] for i in range(7)]
        ends = [S_val[i] + durations[i] - 1 for i in range(7)]
        
        itinerary = []
        for d in range(1, 16):
            cities_today = []
            for i in range(7):
                if S_val[i] <= d <= ends[i]:
                    cities_today.append(city_sequence[i])
            for city in cities_today:
                itinerary.append({"day": d, "city": city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()