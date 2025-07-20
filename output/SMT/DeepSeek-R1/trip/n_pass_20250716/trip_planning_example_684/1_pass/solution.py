from z3 import *

def main():
    # City indices: 0:Amsterdam, 1:Edinburgh, 2:Brussels, 3:Vienna, 4:Berlin, 5:Reykjavik
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    req_array = [4, 5, 5, 5, 4, 5]
    flight_pairs = [
        (0, 1), (0, 3), (0, 4), (0, 5),
        (1, 2), (1, 4),
        (2, 3), (2, 4), (2, 5),
        (3, 4), (3, 5),
        (4, 5)
    ]
    
    # Create Z3 variables for the order of cities (6 segments)
    order = [Int(f"order_{i}") for i in range(6)]
    s = Solver()
    
    # Each order[i] must be between 0 and 5, and all must be distinct
    for i in range(6):
        s.add(And(order[i] >= 0, order[i] < 6))
    s.add(Distinct(order))
    
    # Function to get the required days for a city index
    def get_req(idx):
        return If(idx == 0, 4,
              If(idx == 1, 5,
              If(idx == 2, 5,
              If(idx == 3, 5,
              If(idx == 4, 4, 5)))))
    
    # Flight days: d1, d2, d3, d4, d5
    d1 = get_req(order[0])
    d2 = d1 + get_req(order[1]) - 1
    d3 = d2 + get_req(order[2]) - 1
    d4 = d3 + get_req(order[3]) - 1
    d5 = d4 + get_req(order[4]) - 1
    
    # Ensure flight days are within bounds
    s.add(d5 >= 1, d5 <= 23)
    
    # Function to check if two cities have a direct flight
    def unordered_in(a, b, pairs):
        conditions = []
        for (x, y) in pairs:
            conditions.append(Or(And(a == x, b == y), And(a == y, b == x)))
        return Or(conditions)
    
    # Flight constraints between consecutive segments
    for i in range(5):
        s.add(unordered_in(order[i], order[i+1], flight_pairs))
    
    # Temporal constraints for Amsterdam (city0)
    ams_constraint = Or(
        And(order[0] == 0, 1 <= 8, d1 >= 5),
        And(order[1] == 0, d1 <= 8, d2 >= 5),
        And(order[2] == 0, d2 <= 8, d3 >= 5),
        And(order[3] == 0, d3 <= 8, d4 >= 5),
        And(order[4] == 0, d4 <= 8, d5 >= 5),
        And(order[5] == 0, d5 <= 8)
    )
    s.add(ams_constraint)
    
    # Temporal constraints for Berlin (city4)
    ber_constraint = Or(
        And(order[0] == 4, 1 <= 19, d1 >= 16),
        And(order[1] == 4, d1 <= 19, d2 >= 16),
        And(order[2] == 4, d2 <= 19, d3 >= 16),
        And(order[3] == 4, d3 <= 19, d4 >= 16),
        And(order[4] == 4, d4 <= 19, d5 >= 16),
        And(order[5] == 4, d5 <= 19)
    )
    s.add(ber_constraint)
    
    # Temporal constraints for Reykjavik (city5)
    rey_constraint = Or(
        And(order[0] == 5, 1 <= 16, d1 >= 12),
        And(order[1] == 5, d1 <= 16, d2 >= 12),
        And(order[2] == 5, d2 <= 16, d3 >= 12),
        And(order[3] == 5, d3 <= 16, d4 >= 12),
        And(order[4] == 5, d4 <= 16, d5 >= 12),
        And(order[5] == 5, d5 <= 16)
    )
    s.add(rey_constraint)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(6)]
        
        # Compute flight days
        d1_val = req_array[order_vals[0]]
        d2_val = d1_val + req_array[order_vals[1]] - 1
        d3_val = d2_val + req_array[order_vals[2]] - 1
        d4_val = d3_val + req_array[order_vals[3]] - 1
        d5_val = d4_val + req_array[order_vals[4]] - 1
        
        # Build itinerary
        starts = [1, d1_val, d2_val, d3_val, d4_val, d5_val]
        ends = [d1_val, d2_val, d3_val, d4_val, d5_val, 23]
        itinerary_list = []
        
        for i in range(6):
            city_name = cities[order_vals[i]]
            start = starts[i]
            end = ends[i]
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city_name})
            if i < 5:
                next_city = cities[order_vals[i+1]]
                itinerary_list.append({"day_range": f"Day {end}", "place": city_name})
                itinerary_list.append({"day_range": f"Day {end}", "place": next_city})
        
        # Output the result
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()