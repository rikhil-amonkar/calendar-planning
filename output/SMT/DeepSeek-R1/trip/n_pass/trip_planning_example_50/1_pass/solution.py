from z3 import *

def main():
    days = 12
    # Create Boolean variables for each day and city
    V = [Bool('V_%d' % (i+1)) for i in range(days)]  # Vilnius
    M = [Bool('M_%d' % (i+1)) for i in range(days)]  # Munich
    K = [Bool('K_%d' % (i+1)) for i in range(days)]  # Mykonos

    s = Solver()

    # Start constraint: Day 1 in Vilnius only
    s.add(V[0] == True)
    s.add(M[0] == False)
    s.add(K[0] == False)

    # Total days constraint
    s.add(Sum([If(V[i], 1, 0) for i in range(days)]) == 4)
    s.add(Sum([If(M[i], 1, 0) for i in range(days)]) == 3)
    s.add(Sum([If(K[i], 1, 0) for i in range(days)]) == 7)

    # Day configuration constraint: each day must be one of the valid configurations
    for i in range(days):
        s.add(Or(
            And(V[i], Not(M[i]), Not(K[i])),  # Only Vilnius
            And(M[i], Not(V[i]), Not(K[i])),  # Only Munich
            And(K[i], Not(V[i]), Not(M[i])),  # Only Mykonos
            And(V[i], M[i], Not(K[i])),       # Vilnius and Munich
            And(M[i], K[i], Not(V[i]))        # Munich and Mykonos
        ))

    # Consecutive days must share at least one city
    for i in range(days-1):
        s.add(Or(
            And(V[i], V[i+1]),
            And(M[i], M[i+1]),
            And(K[i], K[i+1])
        ))

    # Special constraints for Vilnius->Munich flight (unidirectional)
    for i in range(1, days):  # For days 2 to 12 (1-indexed)
        s.add(Implies(And(V[i], M[i]), 
                      And(V[i-1], Not(M[i-1]), Not(K[i-1]))))
    
    for i in range(0, days-1):  # For days 1 to 11 (1-indexed)
        s.add(Implies(And(V[i], M[i]), Not(V[i+1])))

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            if is_true(model[V[i]]):
                itinerary.append({"day": day_num, "city": "Vilnius"})
            if is_true(model[M[i]]):
                itinerary.append({"day": day_num, "city": "Munich"})
            if is_true(model[K[i]]):
                itinerary.append({"day": day_num, "city": "Mykonos"})
        
        result = {
            "itinerary": itinerary
        }
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()