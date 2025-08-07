from z3 import *

def main():
    # Define the City enumeration
    City = Datatype('City')
    City.declare('Hamburg')
    City.declare('Munich')
    City.declare('Manchester')
    City.declare('Lyon')
    City.declare('Split')
    City = City.create()
    
    Hamburg = City.Hamburg
    Munich = City.Munich
    Manchester = City.Manchester
    Lyon = City.Lyon
    Split = City.Split
    
    # Define the directed flight edges
    edges = [
        (Split, Munich),
        (Munich, Split),
        (Munich, Manchester),
        (Manchester, Munich),
        (Hamburg, Manchester),
        (Manchester, Hamburg),
        (Hamburg, Munich),
        (Munich, Hamburg),
        (Split, Lyon),
        (Lyon, Split),
        (Lyon, Munich),
        (Munich, Lyon),
        (Hamburg, Split),
        (Split, Hamburg),
        (Manchester, Split)
    ]
    
    # Create solver
    s = Solver()
    
    # Create variables for each day (20 days, index 0 to 19)
    c = [Const(f'c_{i}', City) for i in range(20)]
    
    # Fixed constraints: 
    # Day 13 (index 12) and Day 14 (index 13) in Lyon
    s.add(c[12] == Lyon)
    s.add(c[13] == Lyon)
    # Day 19 (index 18) and Day 20 (index 19) in Manchester
    s.add(c[18] == Manchester)
    s.add(c[19] == Manchester)
    
    # Flight constraints: for each consecutive day pair
    for i in range(0, 19):
        # If the cities are different, then the flight (c[i] to c[i+1]) must be in the allowed edges
        current_city = c[i]
        next_city = c[i+1]
        s.add(If(current_city != next_city, 
                 Or([And(current_city == A, next_city == B) for (A, B) in edges]), 
                 True))
    
    # Function to compute total days for a city
    def total_days_for_city(city):
        # Day 1: base
        base = If(c[0] == city, 1, 0)
        # Days 2 to 20: the end of each day
        middle = Sum([If(c[i] == city, 1, 0) for i in range(1, 20)])
        # Extra: for each flight day, if we start in `city` and leave to another city
        extra_terms = []
        for i in range(0, 19):
            # On the flight day (i+1), if we start in `city` (which is the end of day i) and fly to a different city
            term = If(And(c[i] == city, c[i+1] != city), 1, 0)
            extra_terms.append(term)
        extra = Sum(extra_terms)
        return base + middle + extra
    
    # Total days constraints
    s.add(total_days_for_city(Hamburg) == 7)
    s.add(total_days_for_city(Munich) == 6)
    s.add(total_days_for_city(Manchester) == 2)
    s.add(total_days_for_city(Lyon) == 2)
    s.add(total_days_for_city(Split) == 7)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for i in range(20):
            city_val = model.evaluate(c[i])
            city_name = None
            if city_val.eq(Hamburg):
                city_name = "Hamburg"
            elif city_val.eq(Munich):
                city_name = "Munich"
            elif city_val.eq(Manchester):
                city_name = "Manchester"
            elif city_val.eq(Lyon):
                city_name = "Lyon"
            elif city_val.eq(Split):
                city_name = "Split"
            else:
                city_name = "Unknown"
            itinerary_list.append({"day": i+1, "place": city_name})
        
        # Format as JSON dictionary
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()