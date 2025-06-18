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

    # Define allowed flights (both directions for bidirectional, and directed for Reykjavik to Madrid)
    allowed_flights = set()
    # Bidirectional flights
    bidirectional_pairs = [
        (6, 0), (0, 6),   # Warsaw and Reykjavik
        (2, 5), (5, 2),   # Oslo and Madrid
        (6, 1), (1, 6),   # Warsaw and Riga
        (3, 7), (7, 3),   # Lyon and London
        (5, 7), (7, 5),   # Madrid and London
        (6, 7), (7, 6),   # Warsaw and London
        (6, 2), (2, 6),   # Warsaw and Oslo
        (2, 4), (4, 2),   # Oslo and Dubrovnik
        (2, 0), (0, 2),   # Oslo and Reykjavik
        (1, 2), (2, 1),   # Riga and Oslo
        (2, 3), (3, 2),   # Oslo and Lyon
        (2, 7), (7, 2),   # Oslo and London
        (7, 0), (0, 7),   # London and Reykjavik
        (6, 5), (5, 6),   # Warsaw and Madrid
        (5, 3), (3, 5),   # Madrid and Lyon
        (4, 5), (5, 4)    # Dubrovnik and Madrid
    ]
    for pair in bidirectional_pairs:
        allowed_flights.add(pair)
    # Directed flight: Reykjavik to Madrid
    allowed_flights.add((0, 5))

    s = Solver()

    # at[0] to at[18]: 19 variables representing the city at the end of each day
    at = [Int('at_%d' % i) for i in range(19)]
    
    # Each at variable must be a valid city index (0-7)
    for a in at:
        s.add(a >= 0, a <= 7)
    
    # Flight constraints: consecutive days must either stay or take an allowed flight
    for d in range(18):
        stay_condition = (at[d] == at[d+1])
        flight_condition = Or([And(at[d] == i, at[d+1] == j) for (i, j) in allowed_flights])
        s.add(Or(stay_condition, flight_condition))
    
    # Total travel days must be 7 (since 18 days + 7 travel days = 25 required city-days)
    travel_days = [If(at[d] != at[d+1], 1, 0) for d in range(18)]
    s.add(Sum(travel_days) == 7)
    
    # Constraints for total days per city
    for city_idx in range(8):
        total = 0
        for d in range(1, 19):  # Days 1 to 18
            # Count day if either start or end city matches
            total += If(Or(at[d-1] == city_idx, at[d] == city_idx), 1, 0)
        s.add(total == required_days[city_idx])
    
    # Event constraints: 
    s.add(at[4] == Riga)       # In Riga at the end of day 4 (covers event between day 4 and 5)
    s.add(at[7] == Dubrovnik)  # In Dubrovnik at the end of day 7 (covers event between day 7 and 8)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        at_vals = [m.evaluate(at[i]) for i in range(19)]
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