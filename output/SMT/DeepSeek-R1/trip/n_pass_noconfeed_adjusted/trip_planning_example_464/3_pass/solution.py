from z3 import *

def main():
    cities = ["Naples", "Krakow", "Frankfurt", "Dubrovnik", "Oslo"]
    required_days = [5, 5, 4, 5, 3]
    flights = [(3, 4), (2, 1), (2, 4), (3, 2), (1, 4), (0, 4), (0, 3), (0, 2)]
    
    s = Solver()
    
    # Order of cities (permutation)
    order = [Int(f"order_{i}") for i in range(5)]
    for i in range(5):
        s.add(And(order[i] >= 0, order[i] <= 4))
    s.add(Distinct(order))
    s.add(order[4] == 4)  # Oslo is last
    
    # Arrival and departure days for each city in the itinerary
    A = [Int(f"A_{i}") for i in range(5)]  # Arrival days
    D = [Int(f"D_{i}") for i in range(5)]  # Departure days
    
    # First city arrival is day 1
    s.add(A[0] == 1)
    
    # Last city departure is day 18
    s.add(D[4] == 18)
    
    # Function to get required days using Z3 expressions
    def get_req_days(idx):
        return If(idx == 0, required_days[0],
               If(idx == 1, required_days[1],
               If(idx == 2, required_days[2],
               If(idx == 3, required_days[3], required_days[4]))))
    
    # Constraints for each city
    for i in range(5):
        R = get_req_days(order[i])
        s.add(D[i] == A[i] + R + 1)
    
    # Constraints between consecutive cities
    for i in range(4):
        s.add(A[i+1] == D[i])
    
    # Dubrovnik must cover days 5-9: arrival <= 5 and departure >= 10
    for i in range(5):
        s.add(If(order[i] == 3, And(A[i] <= 5, D[i] >= 10), True))
    
    # Flight connections between consecutive cities
    for i in range(4):
        city_i = order[i]
        city_j = order[i+1]
        flight_exists = Or(
            *[Or(And(city_i == a, city_j == b), And(city_i == b, city_j == a)) for (a, b) in flights]
        )
        s.add(flight_exists)
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(5)]
        A_val = [m.evaluate(A[i]).as_long() for i in range(5)]
        D_val = [m.evaluate(D[i]).as_long() for i in range(5)]
        
        itinerary = []
        for i in range(5):
            city_index = order_val[i]
            city_name = cities[city_index]
            begin_day = A_val[i]
            end_day = D_val[i] - 1  // last day of stay
            day_range = f"Day {begin_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()