from z3 import *
import json

def main():
    # Define the cities and their indices
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    n = len(cities)
    
    # Define allowed directed flights (both directions for each pair)
    edges_list = [
        ["Nice", "Dublin"],
        ["Dublin", "Frankfurt"],
        ["Dublin", "Krakow"],
        ["Krakow", "Frankfurt"],
        ["Lyon", "Frankfurt"],
        ["Nice", "Frankfurt"],
        ["Lyon", "Dublin"],
        ["Nice", "Lyon"]
    ]
    # Map city names to indices
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    allowed_directed = []
    for edge in edges_list:
        a, b = edge
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        allowed_directed.append((a_idx, b_idx))
        allowed_directed.append((b_idx, a_idx))
    
    # Create solver and variables for each day (20 days)
    s = Solver()
    x = [Int('x_%d' % i) for i in range(20)]
    
    # Constraint: each day must be one of the city indices (0 to 4)
    for i in range(20):
        s.add(And(x[i] >= 0, x[i] < n))
    
    # Constraint: consecutive days must either stay in the same city or use a direct flight
    for i in range(1, 20):
        current_city = x[i]
        prev_city = x[i-1]
        same_city = (prev_city == current_city)
        flight_ok = Or([And(prev_city == a, current_city == b) for (a, b) in allowed_directed])
        s.add(Or(same_city, flight_ok))
    
    # Function to compute days in a city
    def days_in_city(c):
        total = If(x[0] == c, 1, 0)
        for i in range(1, 20):
            cond = Or(x[i] == c, And(x[i-1] == c, x[i] != c))
            total = total + If(cond, 1, 0)
        return total
    
    # Constraints for days in each city
    s.add(days_in_city(city_to_index["Nice"]) == 5)
    s.add(days_in_city(city_to_index["Krakow"]) == 6)
    s.add(days_in_city(city_to_index["Dublin"]) == 7)
    s.add(days_in_city(city_to_index["Lyon"]) == 4)
    s.add(days_in_city(city_to_index["Frankfurt"]) == 2)
    
    # Constraint: Nice must have at least one day between day 1 and 5 (inclusive)
    nice_cond = []
    # Day 1 (index 0)
    nice_cond.append(x[0] == city_to_index["Nice"])
    # Days 2 to 5 (indices 1 to 4)
    for i in range(1, 5):
        cond = Or(x[i] == city_to_index["Nice"], And(x[i-1] == city_to_index["Nice"], x[i] != city_to_index["Nice"]))
        nice_cond.append(cond)
    s.add(Or(nice_cond))
    
    # Constraint: Frankfurt must have at least one day between day 19 and 20 (inclusive)
    frankfurt_cond = []
    # Day 19 (index 18)
    cond19 = Or(x[18] == city_to_index["Frankfurt"], And(x[17] == city_to_index["Frankfurt"], x[18] != city_to_index["Frankfurt"]))
    # Day 20 (index 19)
    cond20 = Or(x[19] == city_to_index["Frankfurt"], And(x[18] == city_to_index["Frankfurt"], x[19] != city_to_index["Frankfurt"]))
    frankfurt_cond.append(cond19)
    frankfurt_cond.append(cond20)
    s.add(Or(frankfurt_cond))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(20):
            city_idx = m.evaluate(x[i]).as_long()
            city_name = cities[city_idx]
            itinerary.append({"day": i+1, "place": city_name})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()