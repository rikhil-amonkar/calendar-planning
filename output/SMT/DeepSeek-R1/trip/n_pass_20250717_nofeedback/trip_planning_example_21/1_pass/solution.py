import z3
import json

def main():
    M = [z3.Bool(f"M_{i}") for i in range(1, 11)]
    V = [z3.Bool(f"V_{i}") for i in range(1, 11)]
    C = [z3.Bool(f"C_{i}") for i in range(1, 11)]
    
    s = z3.Solver()
    
    # Each day must be in at least one city
    for i in range(10):
        s.add(z3.Or(M[i], V[i], C[i]))
    
    # No day can be in both Mykonos and Venice
    for i in range(10):
        s.add(z3.Not(z3.And(M[i], C[i])))
    
    # Total days in each city
    s.add(z3.Sum([z3.If(M[i], 1, 0) for i in range(10)]) == 2)
    s.add(z3.Sum([z3.If(V[i], 1, 0) for i in range(10)]) == 4)
    s.add(z3.Sum([z3.If(C[i], 1, 0) for i in range(10)]) == 6)
    
    # Venice must be visited at least once between day 5 and 10 (days 5 to 10 inclusive, indices 4 to 9)
    s.add(z3.Or([C[i] for i in range(4, 10)]))
    
    # Continuity: consecutive days must share at least one city
    for i in range(9):
        s.add(z3.Or(
            z3.And(M[i], M[i+1]),
            z3.And(V[i], V[i+1]),
            z3.And(C[i], C[i+1])
        ))
    
    if s.check() == z3.sat:
        model = s.model()
        itinerary_list = []
        for i in range(10):
            if z3.is_true(model.eval(M[i])):
                itinerary_list.append({"day": i+1, "city": "Mykonos"})
            if z3.is_true(model.eval(V[i])):
                itinerary_list.append({"day": i+1, "city": "Vienna"})
            if z3.is_true(model.eval(C[i])):
                itinerary_list.append({"day": i+1, "city": "Venice"})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print('No solution found')

if __name__ == "__main__":
    main()