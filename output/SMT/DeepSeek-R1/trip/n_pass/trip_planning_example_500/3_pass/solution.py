from z3 import *
import json

def main():
    # Define the City enumeration
    City = Datatype('City')
    City.declare('Hamburg')
    City.declare('Munich')  # Note: Using 'Munich' to match the problem's flight constraints
    City.declare('Manchester')
    City.declare('Lyon')
    City.declare('Split')
    City = City.create()
    
    Hamburg = City.Hamburg
    Munich = City.Munich  # Alias for clarity
    Manchester = City.Manchester
    Lyon = City.Lyon
    Split = City.Split
    
    city_names = {
        Hamburg: "Hamburg",
        Munich: "Munich",
        Manchester: "Manchester",
        Lyon: "Lyon",
        Split: "Split"
    }
    
    # Define directed flights based on the problem
    directed_flights = set()
    
    # Bidirectional flights
    bidirectional_pairs = [
        (Split, Munich),
        (Munich, Manchester),
        (Hamburg, Manchester),
        (Hamburg, Munich),
        (Split, Lyon),
        (Lyon, Munich),
        (Hamburg, Split)
    ]
    
    for (a, b) in bidirectional_pairs:
        directed_flights.add((a, b))
        directed_flights.add((b, a))
    
    # Directed flight from Manchester to Split
    directed_flights.add((Manchester, Split))
    
    # Create start and end variables for 20 days
    start = [Const('start_%d' % i, City) for i in range(1, 21)]
    end = [Const('end_%d' % i, City) for i in range(1, 21)]
    
    s = Solver()
    
    # Constraint 1: Chain constraint (end of day i must equal start of day i+1)
    for i in range(19):
        s.add(end[i] == start[i+1])
    
    # Constraint 2: Flight constraints
    for i in range(20):
        # If start[i] != end[i], then (start[i], end[i]) must be in directed_flights
        flight_taken = (start[i] != end[i])
        valid_flight = Or([And(start[i] == c1, end[i] == c2) for (c1, c2) in directed_flights])
        s.add(Implies(flight_taken, valid_flight))
    
    # Constraint 3: Specific day constraints
    # End of day 13 (index 12) must be Lyon
    s.add(end[12] == Lyon)
    # End of day 19 (index 18) must be Manchester
    s.add(end[18] == Manchester)
    
    # Constraint 4: Total days per city
    required_days = {
        Hamburg: 7,
        Munich: 6,
        Manchester: 2,
        Lyon: 2,
        Split: 7
    }
    
    for city, req in required_days.items():
        total_days = 0
        for i in range(20):
            # Count the day if:
            # - The day starts in the city, OR
            # - The day ends in the city and started in a different city
            count_cond = Or(start[i] == city, And(end[i] == city, start[i] != city))
            total_days += If(count_cond, 1, 0)
        s.add(total_days == req)
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            day = i + 1
            s_val = model.eval(start[i])
            e_val = model.eval(end[i])
            s_name = city_names[s_val]
            e_name = city_names[e_val]
            if s_val == e_val:
                cities_of_day = [s_name]
            else:
                cities_of_day = [s_name, e_name]
            itinerary.append({"day": day, "city": cities_of_day})
        
        # Output the itinerary in JSON format
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()