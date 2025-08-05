from z3 import *

def main():
    # Define the string sort and the 13 variables: city0 to city12
    StringSort = StringSort()
    cities_var = [Const(f'city{i}', StringSort) for i in range(13)]
    
    # Allowed directed flight pairs (both directions for undirected edges)
    undirected_pairs = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki")
    ]
    allowed_directed_pairs = []
    for (a, b) in undirected_pairs:
        allowed_directed_pairs.append((a, b))
        allowed_directed_pairs.append((b, a))
    
    s = Solver()
    constraints = []
    
    # Flight constraints for i in range 1 to 12 (between city_{i-1} and city_i)
    for i in range(1, 13):
        prev = cities_var[i-1]
        curr = cities_var[i]
        stay = (prev == curr)
        flight_options = [And(prev == StringVal(a), curr == StringVal(b)) for (a, b) in allowed_directed_pairs]
        flight = Or(flight_options)
        constraints.append(Or(stay, flight))
    
    # Count constraints for each city
    def count_days(city_name):
        terms = []
        city_val = StringVal(city_name)
        for i in range(1, 13):
            prev = cities_var[i-1]
            curr = cities_var[i]
            terms.append(If(Or(prev == city_val, curr == city_val), 1, 0))
        return terms
    
    prague_days = count_days("Prague")
    naples_days = count_days("Naples")
    helsinki_days = count_days("Helsinki")
    frankfurt_days = count_days("Frankfurt")
    lyon_days = count_days("Lyon")
    
    constraints.append(Sum(prague_days) == 2)
    constraints.append(Sum(naples_days) == 4)
    constraints.append(Sum(helsinki_days) == 4)
    constraints.append(Sum(frankfurt_days) == 3)
    constraints.append(Sum(lyon_days) == 3)
    
    # Fixed events: Prague must be visited on day1 and day2
    constraints.append(Or(cities_var[0] == StringVal("Prague"), cities_var[1] == StringVal("Prague")))
    constraints.append(Or(cities_var[1] == StringVal("Prague"), cities_var[2] == StringVal("Prague")))
    
    # Fixed events: Helsinki must be visited on days 2,3,4,5 and not on day1 or day6
    constraints.append(And(cities_var[0] != StringVal("Helsinki"), cities_var[1] != StringVal("Helsinki")))
    constraints.append(cities_var[2] == StringVal("Helsinki"))
    constraints.append(Or(cities_var[4] == StringVal("Helsinki"), cities_var[5] == StringVal("Helsinki")))
    constraints.append(And(cities_var[5] != StringVal("Helsinki"), cities_var[6] != StringVal("Helsinki")))
    
    # Add all constraints to the solver
    s.add(constraints)
    
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for day in range(1, 13):  # days 1 to 12
            loc = m[cities_var[day]]
            if is_string_value(loc):
                loc_str = loc.as_string()
            else:
                loc_str = str(loc)
            itinerary_list.append({"day": day, "location": loc_str})
        
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("Unsatisfiable")

def is_string_value(v):
    return isinstance(v, StringVal)

if __name__ == "__main__":
    main()