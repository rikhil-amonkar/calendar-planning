from z3 import *

def solve_itinerary():
    s = Solver()
    
    # Days 1-7
    days = range(1, 8)
    # Cities: Riga (0), Amsterdam (1), Mykonos (2)
    R, A, M = 0, 1, 2
    
    # Variables for each day's city
    city = [Int(f'city_{d}') for d in days]
    
    # Possible cities
    for d in days:
        s.add(Or(city[d-1] == R, city[d-1] == A, city[d-1] == M))
    
    # Must be in Riga on days 1 and 2
    s.add(city[0] == R)
    s.add(city[1] == R)
    
    # Flight transitions
    for d in range(1, 7):
        prev = city[d-1]
        curr = city[d]
        # Can stay or take direct flights
        s.add(Or(
            prev == curr,  # Stay
            And(prev == R, curr == A),  # R->A
            And(prev == A, curr == R),  # A->R
            And(prev == A, curr == M),  # A->M
            And(prev == M, curr == A)   # M->A
        ))
    
    # Count days in each city
    count_R = Sum([If(city[d-1] == R, 1, 0) for d in days])
    count_A = Sum([If(city[d-1] == A, 1, 0) for d in days])
    count_M = Sum([If(city[d-1] == M, 1, 0) for d in days])
    
    s.add(count_R == 2)
    s.add(count_A == 2)
    s.add(count_M == 5)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {R: 'Riga', A: 'Amsterdam', M: 'Mykonos'}
        for d in days:
            c = model[city[d-1]].as_long()
            itinerary.append({"day": d, "place": city_names[c]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

print(solve_itinerary())