from z3 import *

def main():
    s = Solver()
    n_days = 16
    cities = ["London", "Oslo", "Split", "Porto"]
    I = [Int(f"I_{i}") for i in range(n_days)]
    
    # City assignments must be valid
    for i in range(n_days):
        s.add(0 <= I[i], I[i] <= 3)
    
    # Split must be on days 7-11 (indices 6-10)
    for i in range(6, 11):
        s.add(I[i] == 2)
    
    # Flight connections
    valid_transitions = [
        (0, 1), (1, 0),  # London-Oslo
        (0, 2), (2, 0),  # London-Split
        (1, 2), (2, 1),  # Oslo-Split
        (1, 3), (3, 1)   # Oslo-Porto
    ]
    for i in range(1, n_days):
        s.add(Or(
            I[i] == I[i-1],  # Stay in same city
            *[And(I[i-1] == a, I[i] == b) for (a, b) in valid_transitions]
        ))
    
    # Presence matrix
    presence = [[Bool(f"pres_{c}_{i}") for i in range(n_days)] for c in range(4)]
    
    for i in range(n_days):
        for c in range(4):
            # Present if current city is c OR traveling from c
            current_city = (I[i] == c)
            traveling_from = And(i > 0, I[i] != I[i-1], I[i-1] == c)
            s.add(presence[c][i] == Or(current_city, traveling_from))
    
    # Total days constraints
    s.add(Sum([If(presence[0][i], 1, 0) for i in range(n_days)]) == 7)  # London
    s.add(Sum([If(presence[1][i], 1, 0) for i in range(n_days)]) == 2)  # Oslo
    s.add(Sum([If(presence[2][i], 1, 0) for i in range(n_days)]) == 5)  # Split
    s.add(Sum([If(presence[3][i], 1, 0) for i in range(n_days)]) == 5)  # Porto
    
    # London presence in first 7 days
    s.add(Or([presence[0][i] for i in range(7)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = m.eval(I[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()