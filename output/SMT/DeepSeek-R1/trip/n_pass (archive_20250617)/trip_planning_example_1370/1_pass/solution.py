from z3 import *

def main():
    # Cities and their indices
    cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
    days_required = [5, 5, 5, 3, 5, 2, 4, 5, 4]
    
    # Mapping city names to indices
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Build the directed flight graph
    graph = set()
    
    # Bidirectional flights: add both directions
    bidirectional = [
        ("Paris", "Krakow"),
        ("Paris", "Amsterdam"),
        ("Paris", "Split"),
        ("Paris", "Geneva"),
        ("Amsterdam", "Geneva"),
        ("Munich", "Split"),
        ("Split", "Krakow"),
        ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"),
        ("Split", "Geneva"),
        ("Vilnius", "Split"),
        ("Munich", "Geneva"),
        ("Munich", "Krakow"),
        ("Vilnius", "Amsterdam"),
        ("Budapest", "Paris"),
        ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"),
        ("Budapest", "Geneva"),
        ("Split", "Amsterdam"),
        ("Santorini", "Geneva"),
        ("Amsterdam", "Santorini"),
        ("Munich", "Budapest"),
        ("Munich", "Paris")
    ]
    for a, b in bidirectional:
        u = city_to_index[a]
        v = city_to_index[b]
        graph.add((u, v))
        graph.add((v, u))
    
    # Unidirectional flights
    unidirectional = [
        ("Vilnius", "Munich"),
        ("Krakow", "Vilnius")
    ]
    for a, b in unidirectional:
        u = city_to_index[a]
        v = city_to_index[b]
        graph.add((u, v))
    
    # Initialize Z3 solver and variables
    s = Solver()
    
    # Arrival and departure days for each city
    arrival = [Int(f'arrival_{i}') for i in range(9)]
    departure = [Int(f'departure_{i}') for i in range(9)]
    
    # Stay duration constraints
    for i in range(9):
        s.add(departure[i] == arrival[i] + days_required[i] - 1)
        s.add(arrival[i] >= 1, arrival[i] <= 30)
        s.add(departure[i] >= 1, departure[i] <= 30)
    
    # Event window constraints
    # Santorini (index 0) must be visited between days 25 and 29
    s.add(arrival[0] <= 29, departure[0] >= 25)
    # Krakow (index 1) must be visited between days 18 and 22
    s.add(arrival[1] <= 22, departure[1] >= 18)
    # Paris (index 2) must be visited between days 11 and 15
    s.add(arrival[2] <= 15, departure[2] >= 11)
    
    # Order of cities (permutation)
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    # First city arrives on day 1
    s.add(arrival[order[0]] == 1)
    
    # Consecutive city constraints: arrival of next city = departure of current
    for i in range(1, 9):
        s.add(arrival[order[i]] == departure[order[i-1]])
    
    # Flight connection constraints for consecutive cities
    for i in range(8):
        edge_exists = Or([And(order[i] == u, order[i+1] == v) for (u, v) in graph])
        s.add(edge_exists)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(9)]
        arrival_val = [m.evaluate(arrival[i]).as_long() for i in range(9)]
        departure_val = [m.evaluate(departure[i]).as_long() for i in range(9)]
        
        # Print the itinerary
        print("Trip Plan:")
        for pos in range(9):
            city_idx = order_val[pos]
            city_name = cities[city_idx]
            start_day = arrival_val[city_idx]
            end_day = departure_val[city_idx]
            print(f"Position {pos + 1}: {city_name} from day {start_day} to day {end_day}")
        
        # Print travel details
        print("\nTravel between cities:")
        for pos in range(8):
            from_city = cities[order_val[pos]]
            to_city = cities[order_val[pos+1]]
            travel_day = departure_val[order_val[pos]]
            print(f"Day {travel_day}: Travel from {from_city} to {to_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()