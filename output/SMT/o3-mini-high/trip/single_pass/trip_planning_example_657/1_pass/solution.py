from z3 import *

def solve_schedule():
    # There are 6 cities with the following requirements:
    # Frankfurt: 4 days, Manchester: 4 days, Valencia: 4 days, Naples: 4 days, Oslo: 3 days, Vilnius: 2 days.
    # We use integer codes for the cities:
    #   Frankfurt = 0, Manchester = 1, Valencia = 2, Naples = 3, Oslo = 4, Vilnius = 5
    cities = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]
    
    # For a visit (segment) in a city, the required stay (including the flight‐day overlap if departing)
    req = { 0:4, 1:4, 2:4, 3:4, 4:3, 5:2 }
    
    # There will be 6 segments (one per city) whose durations (with overlap) add up to 21.
    # Since each transfer day is counted for both the previous and next city, the itinerary spans 16 calendar days.
    n = 6

    solver = Solver()

    # For each segment i, we define a start day S_i and an end day E_i.
    # Note: if you fly on day X then that day X is counted for both the leaving city (ends on X) and the arriving city (starts on X).
    S = [Int(f"S_{i}") for i in range(n)]
    E = [Int(f"E_{i}") for i in range(n)]
    
    # Also, for each segment we choose which city is visited.
    # The integer variable order_i represents the city code for the i-th segment.
    order = [Int(f"order_{i}") for i in range(n)]
    
    # It must cover days 1 to 16.
    solver.add(S[0] == 1)
    solver.add(E[n-1] == 16)
    
    # For each segment i, the duration d_i = E_i - S_i + 1 must equal the required days for that city.
    # We “select” the correct required value using nested If’s.
    for i in range(n):
        # Each order[i] must be one of the 6 cities.
        solver.add(Or([order[i] == c for c in range(6)]))
        d = E[i] - S[i] + 1
        solver.add(d == If(order[i] == 0, req[0],
                     If(order[i] == 1, req[1],
                     If(order[i] == 2, req[2],
                     If(order[i] == 3, req[3],
                     If(order[i] == 4, req[4],
                        req[5])))))
    
    # Consecutive segments touch each other: the next segment starts on the same day the previous one ends.
    for i in range(n-1):
        solver.add(S[i+1] == E[i])
    
    # The segments must cover different cities.
    solver.add(Distinct(order))
    
    # Additional fixed conditions from the problem:
    # --------------------------------------------
    # (1) The annual show is held in Frankfurt from day 13 to day 16.
    #     Since the Frankfurt stay is exactly 4 days, the only possibility is to be in Frankfurt in the last segment.
    solver.add(order[n-1] == 0)  # last segment is Frankfurt

    # (2) You attend a wedding in Vilnius between day 12 and day 13.
    #     To allow a flight on day 13 and count day 13 in both cities, we force the Vilnius stay to immediately precede Frankfurt.
    solver.add(order[n-2] == 5)  # second-last segment is Vilnius

    # (3) In order to fly directly from Vilnius to Frankfurt (a listed direct flight), the flight day (day 13) counts for both.
    #     Moreover, to have a valid flight into Vilnius, the previous city must be connected.
    #     The only direct flight from another city into Vilnius (besides Frankfurt) is from Oslo.
    solver.add(order[n-3] == 4)  # third-last segment is Oslo

    # Now, the remaining segments 0, 1, 2 must be a permutation of the remaining three cities: Manchester, Valencia and Naples.
    # Their integer codes are 1, 2, and 3.
    for i in range(3):
        solver.add(Or(order[i] == 1, order[i] == 2, order[i] == 3))
    # Moreover, the segment immediately preceding Oslo (segment 2) must fly directly to Oslo.
    # Direct flights to Oslo from these candidates only exist from Manchester (1) and Naples (3).
    solver.add(Or(order[2] == 1, order[2] == 3))
    
    # Define the allowed direct flight pairs (bidirectional) as given in the problem.
    # The listed direct flights are:
    #   Valencia <-> Frankfurt, Manchester <-> Frankfurt, Naples <-> Manchester, Naples <-> Frankfurt,
    #   Naples <-> Oslo, Oslo <-> Frankfurt, Vilnius <-> Frankfurt, Oslo <-> Vilnius,
    #   Manchester <-> Oslo, Valencia <-> Naples.
    allowed_flights = [
        (0, 2), (2, 0),    # Frankfurt <-> Valencia
        (0, 1), (1, 0),    # Frankfurt <-> Manchester
        (3, 1), (1, 3),    # Naples <-> Manchester
        (3, 0), (0, 3),    # Naples <-> Frankfurt
        (3, 4), (4, 3),    # Naples <-> Oslo
        (4, 0), (0, 4),    # Oslo <-> Frankfurt
        (5, 0), (0, 5),    # Vilnius <-> Frankfurt
        (4, 5), (5, 4),    # Oslo <-> Vilnius
        (1, 4), (4, 1),    # Manchester <-> Oslo
        (2, 3), (3, 2)     # Valencia <-> Naples
    ]
    
    # For every flight (i.e. between consecutive segments) the two cities must be connected by a direct flight.
    for i in range(n-1):
        a = order[i]
        b = order[i+1]
        solver.add(Or([And(a == x, b == y) for (x, y) in allowed_flights]))
    
    # Check if a solution exists.
    if solver.check() == sat:
        model = solver.model()
        segments = []
        # Extract each segment's start and end days and city name.
        for i in range(n):
            s_val = model[S[i]].as_long()
            e_val = model[E[i]].as_long()
            city_index = model[order[i]].as_long()
            segments.append((s_val, e_val, cities[city_index]))
        # For debugging, you can uncomment the next line:
        # print("Segments (start, end, city):", segments)
        
        # Construct the daily itinerary.
        # A day d is “covered” by a segment if S <= d <= E.
        # On flight days (when d equals an end day of one segment and the start day of the next),
        # that day counts for both cities.
        itinerary = []
        for d in range(1, 17):
            day_cities = []
            for (s_val, e_val, city) in segments:
                if s_val <= d <= e_val:
                    day_cities.append(city)
            # If only one city appears that day, output it as a string; if two appear, output as a list.
            if len(day_cities) == 1:
                day_mapping = {"day": d, "city": day_cities[0]}
            else:
                day_mapping = {"day": d, "city": day_cities}
            itinerary.append(day_mapping)
            
        # Build and print the final JSON result.
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve_schedule()