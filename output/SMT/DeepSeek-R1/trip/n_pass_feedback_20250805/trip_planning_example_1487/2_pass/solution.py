from z3 import *
import json

def main():
    # Define the cities (without Mykonos) and their stay durations
    city_list = ['Athens', 'Brussels', 'Copenhagen', 'Dubrovnik', 'Geneva', 'Munich', 'Naples', 'Prague', 'Santorini']
    L_arr = [4, 4, 5, 3, 3, 5, 4, 2, 5]  # durations in the same order as city_list

    # Indexes for cities with event constraints
    j_cop = city_list.index('Copenhagen')
    j_naples = city_list.index('Naples')
    j_athens = city_list.index('Athens')

    # Define direct flights
    direct_flights_strings = [
        "Copenhagen and Dubrovnik", "Brussels and Copenhagen", "Prague and Geneva", "Athens and Geneva",
        "Naples and Dubrovnik", "Athens and Dubrovnik", "Geneva and Mykonos", "Naples and Mykonos",
        "Naples and Copenhagen", "Munich and Mykonos", "Naples and Athens", "Prague and Athens",
        "Santorini and Geneva", "Athens and Santorini", "Naples and Munich", "Prague and Copenhagen",
        "Brussels and Naples", "Athens and Mykonos", "Athens and Copenhagen", "Naples and Geneva",
        "Dubrovnik and Munich", "Brussels and Munich", "Prague and Brussels", "Brussels and Athens",
        "Athens and Munich", "Geneva and Munich", "Copenhagen and Munich", "Brussels and Geneva",
        "Copenhagen and Geneva", "Prague and Munich", "Copenhagen and Santorini", "Naples and Santorini",
        "Geneva and Dubrovnik"
    ]
    
    direct_flights_set = set()
    for s in direct_flights_strings:
        parts = s.split(' and ')
        if len(parts) == 2:
            a, b = parts[0].strip(), parts[1].strip()
            direct_flights_set.add((a, b))
            direct_flights_set.add((b, a))
    
    # Precompute allowed flight connections for consecutive cities
    allowed_jk = set()
    for j in range(9):
        for k in range(9):
            city_j = city_list[j]
            city_k = city_list[k]
            if (city_j, city_k) in direct_flights_set:
                allowed_jk.add((j, k))
    
    allowed_j_mykonos = [j for j in range(9) if (city_list[j], 'Mykonos') in direct_flights_set]
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create a 9x9 grid of Boolean variables: x[i][j] is True if city j is at position i
    x = [[Bool(f'x_{i}_{j}') for j in range(9)] for i in range(9)]
    
    # Each position has exactly one city
    for i in range(9):
        s.add(Sum([If(x[i][j], 1, 0) for j in range(9)]) == 1)
    
    # Each city appears in exactly one position
    for j in range(9):
        s.add(Sum([If(x[i][j], 1, 0) for i in range(9)]) == 1)
    
    # Flight constraints for consecutive positions (0-7)
    for i in range(8):
        or_terms = []
        for (j, k) in allowed_jk:
            or_terms.append(And(x[i][j], x[i+1][k]))
        if or_terms:
            s.add(Or(or_terms))
        else:
            s.add(False)  # No valid flight, make unsat
    
    # Flight constraint from last position (8) to Mykonos
    if allowed_j_mykonos:
        s.add(Or([x[8][j] for j in allowed_j_mykonos]))
    else:
        s.add(False)
    
    # Define symbolic lengths for each position
    L_sym = [Sum([If(x[i][j], L_arr[j], 0) for j in range(9)]) for i in range(9)]
    
    # Define cumulative sums for start days
    cumul_sym = [0] * 10
    for i in range(1, 10):
        cumul_sym[i] = cumul_sym[i-1] + (L_sym[i-1] - 1)
    
    # Define start and end days for each position
    start_i = [1 + cumul_sym[i] for i in range(9)]
    end_i = [start_i[i] + L_sym[i] - 1 for i in range(9)]
    
    # Event constraints
    for i in range(9):
        # Copenhagen: must include a day between 11 and 15
        s.add(Implies(x[i][j_cop], And(start_i[i] <= 15, end_i[i] >= 11)))
        # Naples: must include a day between 5 and 8
        s.add(Implies(x[i][j_naples], And(start_i[i] <= 8, end_i[i] >= 5)))
        # Athens: must include a day between 8 and 11
        s.add(Implies(x[i][j_athens], And(start_i[i] <= 11, end_i[i] >= 8)))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract the city assignment for each position
        assignment = [None] * 9
        for i in range(9):
            for j in range(9):
                if m.evaluate(x[i][j]):
                    assignment[i] = j
                    break
        
        # Compute actual lengths and cumulative sums
        L_actual = [L_arr[j] for j in assignment]
        cumul_actual = [0] * 10
        for i in range(1, 10):
            cumul_actual[i] = cumul_actual[i-1] + (L_actual[i-1] - 1)
        
        start_actual = [1 + cumul_actual[i] for i in range(9)]
        end_actual = [start_actual[i] + L_actual[i] - 1 for i in range(9)]
        
        # Mykonos starts at the end of the last city and lasts 2 days
        start_mykonos = end_actual[8]
        end_mykonos = start_mykonos + 1  # because 2 days: start_mykonos and start_mykonos+1
        
        # Build itinerary
        itinerary = []
        for i in range(9):
            city_name = city_list[assignment[i]]
            itinerary.append({"city": city_name, "start_day": int(start_actual[i]), "end_day": int(end_actual[i])})
        itinerary.append({"city": "Mykonos", "start_day": int(start_mykonos), "end_day": int(end_mykonos)})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()