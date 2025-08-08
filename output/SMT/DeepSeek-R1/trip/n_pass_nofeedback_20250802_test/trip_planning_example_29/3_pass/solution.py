from z3 import *
import json

def main():
    # City encodings
    D = 0  # Dubrovnik
    F = 1  # Frankfurt
    K = 2  # Krakow
    city_names = {D: "Dubrovnik", F: "Frankfurt", K: "Krakow"}
    
    # State variables: s[0] to s[10] (start of day 1 to start of day 11)
    s = [Int('s_%d' % i) for i in range(11)]
    # Flight variables: flight[0] to flight[9] (for day 1 to day 10)
    flight = [Bool('f_%d' % i) for i in range(10)]
    
    solver = Solver()
    
    # Each s[i] must be one of the cities
    for i in range(11):
        solver.add(Or(s[i] == D, s[i] == F, s[i] == K))
    
    # Start in Dubrovnik on day 1
    solver.add(s[0] == D)
    
    # Allowed direct flights: (D,F), (F,D), (F,K), (K,F)
    allowed_flights = [(D, F), (F, D), (F, K), (K, F)]
    for i in range(10):
        no_flight = (s[i+1] == s[i])
        flight_taken = Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_flights])
        solver.add(If(flight[i], flight_taken, no_flight))
    
    # Presence in each city for each day
    inD = [Or(s[i] == D, And(flight[i], s[i+1] == D)) for i in range(10)]
    inF = [Or(s[i] == F, And(flight[i], s[i+1] == F)) for i in range(10)]
    inK = [Or(s[i] == K, And(flight[i], s[i+1] == K)) for i in range(10)]
    
    # Total days in each city
    totalD = Sum([If(inD[i], 1, 0) for i in range(10)])
    totalF = Sum([If(inF[i], 1, 0) for i in range(10)])
    totalK = Sum([If(inK[i], 1, 0) for i in range(10)])
    solver.add(totalD == 7, totalF == 3, totalK == 2)
    
    # Days 9 and 10 must be entirely in Krakow
    solver.add(s[8] == K)  # Start of day 9 in Krakow
    solver.add(s[9] == K)  # Start of day 10 in Krakow
    solver.add(flight[8] == False)  # No flight on day 9
    solver.add(flight[9] == False)  # No flight on day 10
    
    # Total flights must be exactly 2
    total_flights = Sum([If(flight[i], 1, 0) for i in range(10)])
    solver.add(total_flights == 2)
    
    # Solve and output
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for day in range(10):
            cities = []
            if is_true(m.eval(inD[day])):
                cities.append("Dubrovnik")
            if is_true(m.eval(inF[day])):
                cities.append("Frankfurt")
            if is_true(m.eval(inK[day])):
                cities.append("Krakow")
            cities.sort()  # Sort alphabetically
            place_str = ", ".join(cities)
            itinerary.append({"day": day+1, "place": place_str})
        
        # Group consecutive days with identical places
        grouped_itinerary = []
        i = 0
        while i < len(itinerary):
            j = i
            while j < len(itinerary) and itinerary[j]['place'] == itinerary[i]['place']:
                j += 1
            if i == j-1:
                day_range = f"Day {i+1}"
            else:
                day_range = f"Day {i+1}-{j}"
            grouped_itinerary.append({
                'day_range': day_range,
                'place': itinerary[i]['place']
            })
            i = j
        
        result = {"itinerary": grouped_itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()