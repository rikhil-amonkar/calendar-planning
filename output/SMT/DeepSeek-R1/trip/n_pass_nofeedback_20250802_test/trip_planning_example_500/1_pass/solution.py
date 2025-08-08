from z3 import *
import json

def main():
    # Define the City enumeration
    City = Datatype('City')
    City.declare('Hamburg')
    City.declare('Munich')
    City.declare('Manchester')
    City.declare('Lyon')
    City.declare('Split')
    City = City.create()
    
    # Map city names to their Z3 constants
    city_map_str = {
        "Hamburg": City.Hamburg,
        "Munich": City.Munich,
        "Manchester": City.Manchester,
        "Lyon": City.Lyon,
        "Split": City.Split
    }
    
    # Create variables P0 to P20
    P = [Const(f'P{i}', City) for i in range(0,21)]
    
    s = Solver()
    
    # Define the directed flights based on the problem's direct flights
    directed_flights = set()
    bidirectional_edges = [
        ("Split", "Munich"),
        ("Munich", "Manchester"),
        ("Hamburg", "Manchester"),
        ("Hamburg", "Munich"),
        ("Split", "Lyon"),
        ("Lyon", "Munich"),
        ("Hamburg", "Split")
    ]
    unidirectional_edges = [("Manchester", "Split")]
    
    for u, v in bidirectional_edges:
        u_const = city_map_str[u]
        v_const = city_map_str[v]
        directed_flights.add((u_const, v_const))
        directed_flights.add((v_const, u_const))
    
    for u, v in unidirectional_edges:
        u_const = city_map_str[u]
        v_const = city_map_str[v]
        directed_flights.add((u_const, v_const))
    
    # Flight constraints for each day transition
    for i in range(1, 21):
        prev_city = P[i-1]
        curr_city = P[i]
        # If moving cities, ensure a direct flight exists
        flight_constraint = Or([And(prev_city == u, curr_city == v) for (u, v) in directed_flights])
        s.add(If(prev_city != curr_city, flight_constraint, True))
    
    # Function to compute total days in a city
    def total_days(city_const):
        conditions = []
        for i in range(1, 21):
            conditions.append(If(Or(P[i-1] == city_const, P[i] == city_const), 1, 0))
        return Sum(conditions)
    
    # Total days constraints for each city
    s.add(total_days(City.Hamburg) == 7)
    s.add(total_days(City.Munich) == 6)
    s.add(total_days(City.Manchester) == 2)
    s.add(total_days(City.Lyon) == 2)
    s.add(total_days(City.Split) == 7)
    
    # Specific day constraints: Lyon on day 13 and Manchester on day 19
    s.add(P[13] == City.Lyon)  # End of day 13 in Lyon
    s.add(P[19] == City.Manchester)  # End of day 19 in Manchester
    
    # Constraints to ensure Lyon only on days 13 and 14
    for i in range(1, 13):  # Days 1 to 12
        s.add(And(P[i-1] != City.Lyon, P[i] != City.Lyon))
    for i in range(15, 21):  # Days 15 to 20
        s.add(And(P[i-1] != City.Lyon, P[i] != City.Lyon))
    
    # Constraints to ensure Manchester only on days 19 and 20
    for i in range(1, 19):  # Days 1 to 18
        s.add(And(P[i-1] != City.Manchester, P[i] != City.Manchester))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # Map Z3 constants back to city names
        rev_city_map = {
            City.Hamburg: "Hamburg",
            City.Munich: "Munich",
            City.Manchester: "Manchester",
            City.Lyon: "Lyon",
            City.Split: "Split"
        }
        itinerary_list = []
        # The itinerary for day i is the end city of that day (P_i for i in 1..20)
        for day in range(1, 21):
            city_val = model[P[day]]
            city_name = rev_city_map[city_val]
            itinerary_list.append({"day": day, "place": city_name})
        
        result_dict = {"itinerary": itinerary_list}
        print(json.dumps(result_dict))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()