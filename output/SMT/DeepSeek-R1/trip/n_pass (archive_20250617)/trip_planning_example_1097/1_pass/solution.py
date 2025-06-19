from z3 import *

def main():
    # City indices
    Reykjavik = 0
    Riga = 1
    Oslo = 2
    Lyon = 3
    Dubrovnik = 4
    Madrid = 5
    Warsaw = 6
    London = 7

    cities = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]
    
    # Required days per city
    required_days = [4, 2, 3, 5, 2, 2, 4, 3]  # Reykjavik, Riga, Oslo, Lyon, Dubrovnik, Madrid, Warsaw, London

    # Define directed flight edges
    edges = set()
    edges.add((6, 0)); edges.add((0, 6))  # Warsaw-Reykjavik
    edges.add((2, 5)); edges.add((5, 2))  # Oslo-Madrid
    edges.add((6, 1)); edges.add((1, 6))  # Warsaw-Riga
    edges.add((3, 7)); edges.add((7, 3))  # Lyon-London
    edges.add((5, 7)); edges.add((7, 5))  # Madrid-London
    edges.add((6, 7)); edges.add((7, 6))  # Warsaw-London
    edges.add((0, 5))                     # Reykjavik to Madrid (directed)
    edges.add((6, 2)); edges.add((2, 6))  # Warsaw-Oslo
    edges.add((2, 4)); edges.add((4, 2))  # Oslo-Dubrovnik
    edges.add((2, 0)); edges.add((0, 2))  # Oslo-Reykjavik
    edges.add((1, 2)); edges.add((2, 1))  # Riga-Oslo
    edges.add((2, 3)); edges.add((3, 2))  # Oslo-Lyon
    edges.add((2, 7)); edges.add((7, 2))  # Oslo-London
    edges.add((7, 0)); edges.add((0, 7))  # London-Reykjavik
    edges.add((6, 5)); edges.add((5, 6))  # Warsaw-Madrid
    edges.add((5, 3)); edges.add((3, 5))  # Madrid-Lyon
    edges.add((4, 5)); edges.add((5, 4))  # Dubrovnik-Madrid

    s = Solver()

    # at[0] to at[18]: 19 variables representing the city at the end of each day (at[0] is start of day 1)
    at = [Int('at_%d' % i) for i in range(19)]
    
    # Each at variable must be between 0 and 7 (inclusive)
    for a in at:
        s.add(a >= 0, a <= 7)
    
    # Flight constraints: for each consecutive day pair, either stay or take a direct flight
    for d in range(18):
        stay_condition = (at[d] == at[d+1])
        flight_condition = Or([And(at[d] == i, at[d+1] == j) for (i, j) in edges])
        s.add(Or(stay_condition, flight_condition))
    
    # Total travel days must be 7 (since 18 days + 7 travel days = 25 required city-days)
    travel_days = [If(at[d] != at[d+1], 1, 0) for d in range(18)]
    s.add(Sum(travel_days) == 7)
    
    # Constraints for total days per city
    for city_idx in range(8):
        total = 0
        for d in range(1, 19):  # Days 1 to 18
            # Day d involves at[d-1] (start) and at[d] (end)
            total += If(Or(at[d-1] == city_idx, at[d] == city_idx), 1, 0)
        s.add(total == required_days[city_idx])
    
    # Event constraints: Riga on day 4 or 5, Dubrovnik on day 7 or 8
    s.add(Or(Or(at[3] == Riga, at[4] == Riga), Or(at[4] == Riga, at[5] == Riga)))
    s.add(Or(Or(at[6] == Dubrovnik, at[7] == Dubrovnik), Or(at[7] == Dubrovnik, at[8] == Dubrovnik)))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        at_vals = [m.evaluate(at[i]) for i in range(19)]
        
        # Convert Z3 integers to Python integers
        at_vals = [a.as_long() for a in at_vals]
        
        # Print the travel plan
        for d in range(1, 19):
            start_city = at_vals[d-1]
            end_city = at_vals[d]
            if start_city == end_city:
                print(f"Day {d}: stay in {cities[start_city]}")
            else:
                print(f"Day {d}: fly from {cities[start_city]} to {cities[end_city]}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()