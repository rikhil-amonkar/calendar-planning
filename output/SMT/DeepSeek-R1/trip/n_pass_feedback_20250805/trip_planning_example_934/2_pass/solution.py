from z3 import *
import json

def main():
    # City names and their indices
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    # Required days for each city in order: Brussels, Rome, Dubrovnik, Geneva, Budapest, Riga, Valencia
    req = [5, 2, 3, 5, 2, 4, 2]
    
    # Flight connections: list of direct flight pairs (as given)
    flight_pairs = [
        (0, 6), (1, 6), (0, 3), (1, 3), (2, 3), (6, 3), (1, 5), 
        (3, 4), (5, 0), (1, 4), (0, 1), (0, 4), (2, 1)
    ]
    
    # Initialize Z3 solver
    s = Solver()
    
    # Position variables for each city (0 to 6)
    pos = [Int(f'pos_{i}') for i in range(7)]
    # Each position must be between 0 and 6
    for i in range(7):
        s.add(pos[i] >= 0, pos[i] <= 6)
    # All positions distinct
    s.add(Distinct(pos))
    
    # Start and end day variables for each city
    start = [Int(f'start_{i}') for i in range(7)]
    end = [Int(f'end_{i}') for i in range(7)]
    
    # Compute start and end days based on city positions
    for i in range(7):
        # Start day = 1 + sum of (req[j]-1) for all cities j before i in the sequence
        sum_before = 0
        for j in range(7):
            if i == j:
                continue
            # If city j is before city i in the sequence, add (req[j]-1)
            sum_before += If(pos[j] < pos[i], req[j] - 1, 0)
        s.add(start[i] == 1 + sum_before)
        s.add(end[i] == start[i] + req[i] - 1)
    
    # Meeting constraints
    # Brussels (index 0) must have at least one day between 7 and 11 inclusive
    s.add(start[0] <= 11, end[0] >= 7)
    # Budapest (index 4) must have at least one day between 16 and 17 inclusive
    s.add(start[4] <= 17, end[4] >= 16)
    # Riga (index 5) must have at least one day between 4 and 7 inclusive
    s.add(start[5] <= 7, end[5] >= 4)
    
    # Flight constraints for consecutive cities in the sequence
    for i in range(7):
        for j in range(i+1, 7):  # Avoid duplicate pairs by considering j > i
            # If cities i and j are consecutive in the sequence (|pos[i] - pos[j]| == 1)
            is_consecutive = Or(pos[i] == pos[j] + 1, pos[i] == pos[j] - 1)
            # Check if there is a direct flight between i and j
            has_flight = False
            for a, b in flight_pairs:
                # Check if (i,j) matches (a,b) in any order
                has_flight = Or(has_flight, And(i == a, j == b), And(i == b, j == a))
            # If they are consecutive, they must have a direct flight
            s.add(Implies(is_consecutive, has_flight))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract start and end days for each city
        start_val = [m.evaluate(start[i]).as_long() for i in range(7)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(7)]
        
        # Build itinerary: for each day, list the cities the traveler is in
        itinerary = []
        for day in range(1, 18):  # Days 1 to 17
            cities_today = []
            for i in range(7):
                if start_val[i] <= day <= end_val[i]:
                    cities_today.append(cities[i])
            itinerary.append({"day": day, "city": cities_today})
        
        # Output the result as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()