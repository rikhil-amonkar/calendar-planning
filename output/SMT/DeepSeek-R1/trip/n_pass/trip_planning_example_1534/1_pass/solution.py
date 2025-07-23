from z3 import *
import json

def main():
    # Define the City datatype
    City = Datatype('City')
    cities_list = ["Warsaw", "Venice", "Vilnius", "Salzburg", "Amsterdam", "Barcelona", "Paris", "Hamburg", "Florence", "Tallinn"]
    for c in cities_list:
        City.declare(c)
    City = City.create()
    
    # Map city names to their Z3 constants
    city_consts = {name: getattr(City, name) for name in cities_list}
    
    # Define the allowed flights (bidirectional and directed)
    bidirectional = [
        ("Paris", "Venice"), 
        ("Barcelona", "Amsterdam"), 
        ("Amsterdam", "Warsaw"), 
        ("Amsterdam", "Vilnius"), 
        ("Barcelona", "Warsaw"), 
        ("Warsaw", "Venice"), 
        ("Amsterdam", "Hamburg"), 
        ("Barcelona", "Hamburg"), 
        ("Barcelona", "Florence"), 
        ("Barcelona", "Venice"), 
        ("Paris", "Hamburg"), 
        ("Paris", "Vilnius"), 
        ("Paris", "Amsterdam"), 
        ("Paris", "Florence"), 
        ("Florence", "Amsterdam"), 
        ("Vilnius", "Warsaw"), 
        ("Barcelona", "Tallinn"), 
        ("Paris", "Warsaw"), 
        ("Tallinn", "Warsaw"), 
        ("Amsterdam", "Tallinn"), 
        ("Paris", "Tallinn"), 
        ("Paris", "Barcelona"), 
        ("Venice", "Hamburg"), 
        ("Warsaw", "Hamburg"), 
        ("Hamburg", "Salzburg"), 
        ("Amsterdam", "Venice")
    ]
    directed = [("Tallinn", "Vilnius")]
    
    allowed_flights = set()
    for a, b in bidirectional:
        a_const = city_consts[a]
        b_const = city_consts[b]
        allowed_flights.add((a_const, b_const))
        allowed_flights.add((b_const, a_const))
    for a, b in directed:
        a_const = city_consts[a]
        b_const = city_consts[b]
        allowed_flights.add((a_const, b_const))
    
    # Create itinerary variables: I[0] to I[25]
    I = [Const(f'I_{i}', City) for i in range(26)]
    s = Solver()
    
    # Flight constraints: for each day, if the city changes, the flight must be allowed
    for d in range(1, 26):
        prev = I[d-1]
        curr = I[d]
        options = [And(prev == c1, curr == c2) for (c1, c2) in allowed_flights]
        s.add(Or(prev == curr, Or(options)))
    
    # Total days in each city (considering partial days during flights)
    total_days = {}
    for name, c in city_consts.items():
        total = 0
        for d in range(1, 26):  # Calendar days 1 to 25
            total += If(Or(I[d-1] == c, I[d] == c), 1, 0)
        total_days[c] = total
    
    # Add constraints for required stay durations
    s.add(total_days[city_consts["Warsaw"]] == 4)
    s.add(total_days[city_consts["Venice"]] == 3)
    s.add(total_days[city_consts["Vilnius"]] == 3)
    s.add(total_days[city_consts["Salzburg"]] == 4)
    s.add(total_days[city_consts["Amsterdam"]] == 2)
    s.add(total_days[city_consts["Barcelona"]] == 5)
    s.add(total_days[city_consts["Paris"]] == 2)
    s.add(total_days[city_consts["Hamburg"]] == 4)
    s.add(total_days[city_consts["Florence"]] == 5)
    s.add(total_days[city_consts["Tallinn"]] == 2)
    
    # Event constraints
    # Paris workshop on day 1 and 2
    s.add(Or(I[0] == city_consts["Paris"], I[1] == city_consts["Paris"]))
    s.add(Or(I[1] == city_consts["Paris"], I[2] == city_consts["Paris"]))
    
    # Barcelona meeting between day 2 and 6
    s.add(Or([Or(I[d-1] == city_consts["Barcelona"], I[d] == city_consts["Barcelona"]) for d in range(2, 7)]))
    
    # Hamburg conference from day 19 to 22
    for d in range(19, 23):
        s.add(Or(I[d-1] == city_consts["Hamburg"], I[d] == city_consts["Hamburg"]))
    
    # Tallinn meeting between day 11 and 12
    s.add(Or([Or(I[d-1] == city_consts["Tallinn"], I[d] == city_consts["Tallinn"]) for d in range(11, 13)]))
    
    # Salzburg wedding from day 22 to 25
    for d in range(22, 26):
        s.add(Or(I[d-1] == city_consts["Salzburg"], I[d] == city_consts["Salzburg"]))
    
    # Additional constraint: exactly 9 flight days (since total stay days sum to 34 and 25 days + 9 flights = 34)
    flight_days = Sum([If(I[d-1] != I[d], 1, 0) for d in range(1, 26)])
    s.add(flight_days == 9)
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Extract the city for the end of each day (days 1 to 25)
        for d in range(1, 26):
            city_val = m.evaluate(I[d])
            for name, c in city_consts.items():
                if eq(city_val, c):
                    itinerary.append({"day": d, "city": name})
                    break
        # Output the itinerary as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()