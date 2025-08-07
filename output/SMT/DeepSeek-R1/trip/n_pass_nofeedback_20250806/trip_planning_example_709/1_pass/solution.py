from z3 import *
import json

def main():
    # Cities: 0=Dubrovnik, 1=Helsinki, 2=Reykjavik, 3=Prague, 4=Valencia, 5=Porto
    n = 6
    city_names = ["Dubrovnik", "Helsinki", "Reykjavik", "Prague", "Valencia", "Porto"]
    req = [4, 4, 4, 3, 5, 3]  # requirements for cities in order 0 to 5

    # Adjacency matrix for direct flights
    adj = [
        [0, 1, 0, 0, 0, 0],   # Dubrovnik
        [1, 0, 1, 1, 0, 0],   # Helsinki
        [0, 1, 0, 1, 0, 0],   # Reykjavik
        [0, 1, 1, 0, 1, 0],   # Prague
        [0, 0, 0, 1, 0, 1],   # Valencia
        [0, 0, 0, 0, 1, 0]    # Porto
    ]

    s = Solver()
    order = [Int('o%d' % i) for i in range(n)]
    
    # Each city index must be between 0 and 5
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    
    s.add(Distinct(order))
    
    # Flight constraints between consecutive cities
    for idx in range(n-1):
        constraints = []
        for j in range(n):
            for k in range(n):
                if adj[j][k] == 1:
                    constraints.append(And(order[idx] == j, order[idx+1] == k))
        s.add(Or(constraints))
    
    # Constraints for last two cities: Valencia then Porto
    s.add(order[4] == 4)  # Valencia at position 4
    s.add(order[5] == 5)  # Porto at position 5
    s.add(order[3] == 3)  # Prague at position 3 (since only Prague connects to Valencia)

    if s.check() == sat:
        m = s.model()
        ord_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        
        # Compute end days for the first five cities
        e = [0] * 5
        e[0] = req[ord_val[0]]
        for i in range(1, 5):
            e[i] = e[i-1] + req[ord_val[i]] - 1
        
        start_days = [1, e[0], e[1], e[2], e[3], e[4]]
        end_days = [e[0], e[1], e[2], e[3], e[4], 18]
        
        itinerary = []
        for day in range(1, 19):
            for i in range(6):
                if start_days[i] <= day <= end_days[i]:
                    itinerary.append({"day": day, "place": city_names[ord_val[i]]})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()