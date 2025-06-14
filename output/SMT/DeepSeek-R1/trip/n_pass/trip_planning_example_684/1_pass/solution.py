import z3

def main():
    s = z3.Solver()
    n = 6
    city_names = {
        0: "Amsterdam",
        1: "Edinburgh",
        2: "Brussels",
        3: "Vienna",
        4: "Berlin",
        5: "Reykjavik"
    }
    
    # City variables for each segment
    city = [z3.Int(f'city_{i}') for i in range(n)]
    for i in range(n):
        s.add(z3.And(city[i] >= 0, city[i] <= 5))
    s.add(z3.Distinct(city))
    
    # Arrival and departure variables
    arrival = [z3.Int(f'arrival_{i}') for i in range(n)]
    departure = [z3.Int(f'departure_{i}') for i in range(n)]
    
    # Constraints for arrival and departure
    s.add(arrival[0] == 1)
    for i in range(n-1):
        s.add(departure[i] == arrival[i+1])
    s.add(departure[n-1] == 23)
    
    # Stay duration constraints
    stay = [departure[i] - arrival[i] + 1 for i in range(n)]
    for i in range(n):
        c = city[i]
        s.add(z3.Or(
            z3.And(c == 0, stay[i] == 4, arrival[i] <= 5, departure[i] >= 8),
            z3.And(c == 1, stay[i] == 5),
            z3.And(c == 2, stay[i] == 5),
            z3.And(c == 3, stay[i] == 5),
            z3.And(c == 4, stay[i] == 4, arrival[i] <= 16, departure[i] >= 19),
            z3.And(c == 5, stay[i] == 5, arrival[i] <= 12, departure[i] >= 16)
        ))
    
    # Direct flight constraints
    edges_list = [
        (1, 4), (0, 4), (1, 0), (3, 4), (4, 2), (3, 5), 
        (1, 2), (3, 2), (0, 5), (5, 2), (0, 3), (5, 4)
    ]
    allowed_set = set()
    for u, v in edges_list:
        allowed_set.add((u, v))
        allowed_set.add((v, u))
    
    for i in range(n-1):
        s.add(z3.Or([z3.And(city[i] == u, city[i+1] == v) for (u, v) in allowed_set]))
    
    # Check and print solution
    if s.check() == z3.sat:
        model = s.model()
        plan = []
        for i in range(n):
            c_val = model[city[i]].as_long()
            a_val = model[arrival[i]].as_long()
            d_val = model[departure[i]].as_long()
            plan.append((city_names[c_val], a_val, d_val))
        
        print("Trip Plan:")
        for i, (name, a, d) in enumerate(plan):
            print(f"Segment {i+1}: Stay in {name} from day {a} to day {d}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()